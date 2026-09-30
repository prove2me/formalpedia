-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_chart_global_base
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T21:23:12.734487+00:00
-- url     : https://prove2.me/submissions/c36edb93-24d4-4537-8004-223e2f571c5f

import Definitions.Def_WeierstrassEllipticZeta_GlobalChartBase
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.Tactic

noncomputable section
open MvPolynomial Filter
open scoped Topology
namespace WeierstrassEllipticZeta
open TranscendenceTheory

private lemma exists_entire_clearing (d : ℂ → ℂ) (a : Fin 4 → ℂ → ℂ)
    (hd : AnalyticOnNhd ℂ d Set.univ)
    (ha : ∀ i, AnalyticOnNhd ℂ (a i) Set.univ) (p : MvPolynomial (Fin 4) ℂ) :
    ∃ (n : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F Set.univ ∧
      ∀ z, d z ≠ 0 → F z = d z ^ n * eval (fun i => a i z / d z) p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    exact ⟨0, fun _ => c, fun _ _ => analyticAt_const, by simp⟩
  | add p q hp hq =>
    obtain ⟨n, F, hF, heF⟩ := hp
    obtain ⟨m, G, hG, heG⟩ := hq
    refine ⟨n + m, fun z => d z ^ m * F z + d z ^ n * G z, ?_, ?_⟩
    · intro z hz
      exact (((hd z hz).pow m).mul (hF z hz)).add (((hd z hz).pow n).mul (hG z hz))
    · intro z hz
      dsimp only
      rw [heF z hz, heG z hz, map_add, pow_add]
      ring
  | mul_X p i hp =>
    obtain ⟨n, F, hF, heF⟩ := hp
    refine ⟨n + 1, fun z => F z * a i z, ?_, ?_⟩
    · intro z hz
      exact (hF z hz).mul (ha i z hz)
    · intro z hz
      dsimp only
      rw [heF z hz, map_mul, eval_X, pow_succ]
      field_simp

private lemma rational_eval_zero_global (d : ℂ → ℂ) (a : Fin 4 → ℂ → ℂ)
    (hd : AnalyticOnNhd ℂ d Set.univ)
    (ha : ∀ i, AnalyticOnNhd ℂ (a i) Set.univ)
    (p : MvPolynomial (Fin 4) ℂ) (z : ℂ) (hz : d z ≠ 0)
    (hzero : ∀ᶠ w in 𝓝 z, eval (fun i => a i w / d w) p = 0) :
    ∀ w, d w ≠ 0 → eval (fun i => a i w / d w) p = 0 := by
  obtain ⟨n, F, hF, heF⟩ := exists_entire_clearing d a hd ha p
  have hU : IsOpen {w | d w ≠ 0} := hd.continuous.isOpen_preimage _ isOpen_ne
  have hFzero : F = 0 := by
    apply AnalyticOnNhd.eq_of_eventuallyEq hF
      (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
      (z₀ := z)
    filter_upwards [hU.mem_nhds hz, hzero] with w hw hzw
    simp [heF w hw, hzw]
  intro w hw
  have h := heF w hw
  rw [hFzero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero n hw)

private lemma mem_local_kernel (S : Fin 5 → ℂ → ℂ) (c : Fin 2) (z : ℂ)
    (p : MvPolynomial (Fin 4) ℂ) :
    p ∈ analyticOrbitKernel (extensionChartEvalHom S c) z ↔
      ∀ᶠ w in 𝓝 z, eval (extensionChartCoordinates S c w) p = 0 := by
  change ((fun w => eval (extensionChartCoordinates S c w) p) : Germ (𝓝 z) ℂ) = 0 ↔ _
  exact Germ.coe_eq

private lemma mem_global_kernel (S : Fin 5 → ℂ → ℂ) (c : Fin 2)
    (p : MvPolynomial (Fin 4) ℂ) :
    p ∈ extensionGlobalChartKernel S c ↔
      ∀ w, S (extensionChartDenominator c) w ≠ 0 →
        eval (extensionChartCoordinates S c w) p = 0 := by
  simp [extensionGlobalChartKernel, Submodule.mem_iInf, RingHom.mem_ker]

private lemma kernel_globalization (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (c : Fin 2) (z : ℂ) (hz : S (extensionChartDenominator c) z ≠ 0) :
    analyticOrbitKernel (extensionChartEvalHom S c) z = extensionGlobalChartKernel S c := by
  let d := S (extensionChartDenominator c)
  let a : Fin 4 → ℂ → ℂ := fun i w =>
    if c = 0 then ![w * S 0 w, S 1 w, S 2 w, S 3 w] i
    else ![w * S 2 w, S 0 w, S 1 w, S 4 w] i
  have ha : ∀ i, AnalyticOnNhd ℂ (a i) Set.univ := by
    intro i w hw
    have han (j : Fin 5) : AnalyticAt ℂ (S j) w := hS j w hw
    fin_cases c <;> fin_cases i <;> dsimp [a] <;> fun_prop
  have heval (w : ℂ) (hw : d w ≠ 0) :
      extensionChartCoordinates S c w = fun i => a i w / d w := by
    funext i
    fin_cases c <;> fin_cases i <;>
      simp [extensionChartCoordinates, a, d, extensionChartDenominator] at hw ⊢
    all_goals simp [hw]
  have hU : IsOpen {w | d w ≠ 0} := (hS _).continuous.isOpen_preimage _ isOpen_ne
  ext p
  rw [mem_local_kernel, mem_global_kernel]
  constructor
  · intro hp
    have hzero : ∀ᶠ w in 𝓝 z, eval (fun i => a i w / d w) p = 0 := by
      filter_upwards [hU.mem_nhds hz, hp] with w hw hpw
      rwa [← heval w hw]
    intro w hw
    rw [heval w hw]
    exact rational_eval_zero_global d a (hS _) ha p z hz hzero w hw
  · intro hp
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hp w hw


end WeierstrassEllipticZeta

open TranscendenceTheory WeierstrassEllipticZeta

theorem solution
    (S : Fin 5 → ℂ → ℂ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ) :
    (∀ (c : Fin 2) (z : ℂ), S (extensionChartDenominator c) z ≠ 0 →
      analyticOrbitKernel (extensionChartEvalHom S c) z = extensionGlobalChartKernel S c ∧
      ∀ Q : MvPolynomial (Fin 7) ℂ,
        extensionChartBaseIdeal S Q c z = extensionGlobalChartBaseIdeal S Q c) ∧
    ∀ (L : PeriodPair) (Q : MvPolynomial (Fin 7) ℂ) (T : ℕ),
      (globalChartCandidates L S Q T).Finite := by
  constructor
  · intro c z hz
    have h := kernel_globalization S hS c z hz
    refine ⟨h, ?_⟩
    intro Q
    simp only [extensionChartBaseIdeal, analyticOrbitBaseIdeal, extensionGlobalChartBaseIdeal, h]
  · intro L Q T
    have hfin (c : Fin 2) (i : Fin 3) :
        (differentialProlongation (extensionChartDerivation L.g₂ L.g₃ c)
          (extensionGlobalChartBaseIdeal S Q c) (i.val * T)).minimalPrimes.Finite :=
      Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
    have hfamily : (⋃ (c : Fin 2) (i : Fin 3),
        (fun p : Ideal (MvPolynomial (Fin 4) ℂ) => (c, i, p)) ''
          (differentialProlongation (extensionChartDerivation L.g₂ L.g₃ c)
            (extensionGlobalChartBaseIdeal S Q c) (i.val * T)).minimalPrimes).Finite :=
      Set.finite_iUnion fun c => Set.finite_iUnion fun i => (hfin c i).image _
    apply hfamily.subset
    rintro ⟨c, i, p⟩ hp
    exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨i, ⟨p, hp.1, rfl⟩⟩⟩
