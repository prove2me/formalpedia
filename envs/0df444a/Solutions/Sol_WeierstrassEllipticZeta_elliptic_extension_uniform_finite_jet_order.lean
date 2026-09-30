-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_uniform_finite_jet_order
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T20:18:05.877364+00:00
-- url     : https://prove2.me/submissions/385f0a54-f149-46a2-941e-8a739a96b23a

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_chart_normalization
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

noncomputable section
open Filter MvPolynomial
open scoped Topology
open WeierstrassEllipticZeta

private lemma projective_block_scaling (n : ℕ) (Q : MvPolynomial (Fin 7) ℂ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (t a : ℂ) (v : Fin 5 → ℂ) :
    eval ![1, t, a * v 0, a * v 1, a * v 2, a * v 3, a * v 4] Q =
      a ^ n * eval ![1, t, v 0, v 1, v 2, v 3, v 4] Q := by
  classical
  rw [Q.as_sum, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.prod_empty, one_pow, one_mul, mul_one]
  change coeff d Q * (t ^ d 1 * ((a * v 0) ^ d 2 * ((a * v 1) ^ d 3 *
    ((a * v 2) ^ d 4 * ((a * v 3) ^ d 5 * (a * v 4) ^ d 6))))) =
    a ^ n * (coeff d Q * (t ^ d 1 * (v 0 ^ d 2 * (v 1 ^ d 3 *
      (v 2 ^ d 4 * (v 3 ^ d 5 * v 4 ^ d 6))))))
  rw [← hQ d hd]
  simp only [mul_pow, pow_add]
  ring

private lemma finite_polynomial_zero_test (p : ℕ → MvPolynomial (Fin 4) ℂ) :
    ∃ N : ℕ, 0 < N ∧ ∀ v : Fin 4 → ℂ,
      (∀ k < N, eval v (p k) = 0) → ∀ k, eval v (p k) = 0 := by
  let J : ℕ →o Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⟨fun n => Ideal.span (p '' Set.Iio n), fun _ _ h =>
      Ideal.span_mono (Set.image_mono (fun _ hi => lt_of_lt_of_le hi h))⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (MvPolynomial (Fin 4) ℂ) (MvPolynomial (Fin 4) ℂ)) J
  refine ⟨N + 1, by omega, ?_⟩
  intro v hv k
  have hle : J (N + 1) ≤ RingHom.ker (eval v) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact hv i hi
  apply hle
  rw [← hN (N + 1) (by omega), hN (max (N + 1) (k + 1)) (by omega)]
  exact Ideal.subset_span ⟨k, by simp only [Set.mem_Iio]; omega, rfl⟩

theorem solution
    (g₂ g₃ : ℂ) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (R : ℂ → ProjectiveExtensionChartLocus g₂ g₃)
    (hR : ∀ z : ℂ, ∃ hv : (fun j : Fin 5 => S j z) ≠ 0,
      (R z).val.val = Projectivization.mk ℂ (fun j => S j z) hv)
    (hjets : ∀ (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ) (k : ℕ),
      ((extensionChartDerivation g₂ g₃ c)^[k] p).totalDegree ≤ p.totalDegree + k ∧
      ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
        iteratedDeriv k (fun w => eval (extensionChartCoordinates S c w) p) z =
          eval (extensionChartCoordinates S c z) ((extensionChartDerivation g₂ g₃ c)^[k] p) ∧
        ((k : ℕ∞) ≤ analyticOrderAt
            (fun w => eval (extensionChartCoordinates S c w) p) z ↔
          ∀ l < k, eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation g₂ g₃ c)^[l] p) = 0)) :
    ∀ (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ),
      (∀ d ∈ Q.support, d 0 + d 1 = m ∧
        d 2 + d 3 + d 4 + d 5 + d 6 = n) →
      (fun z : ℂ => eval ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
      ∃ N : ℕ, 0 < N ∧
        (∀ z : ℂ, analyticOrderAt
          (fun w : ℂ => eval ![1, w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q) z < (N : ℕ∞)) ∧
        ∀ (c : Fin 2) (z : ℂ), S (extensionChartDenominator c) z ≠ 0 →
          ∃ k < N, eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation g₂ g₃ c)^[k] (extensionChartNormalize c Q)) ≠ 0 := by
  intro m n Q hQ hnonzero
  let F (z : ℂ) := eval ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q
  let f (c : Fin 2) (z : ℂ) :=
    eval (extensionChartCoordinates S c z) (extensionChartNormalize c Q)
  have hnorm := elliptic_extension_projective_chart_normalization g₂ g₃ S hS R hR hjets
  have hFa (z : ℂ) : AnalyticAt ℂ F z := by
    apply AnalyticAt.aeval_mvPolynomial
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_id
    all_goals exact hS _ z (Set.mem_univ _)
  have hfa (c : Fin 2) (z : ℂ) (hz : S (extensionChartDenominator c) z ≠ 0) :
      AnalyticAt ℂ (f c) z := by
    apply AnalyticAt.aeval_mvPolynomial
    intro i
    fin_cases c <;> fin_cases i
    all_goals first
      | exact analyticAt_id
      | exact (hS _ z (Set.mem_univ _)).div (hS _ z (Set.mem_univ _)) hz
  have hratio (z : ℂ) (i j : Fin 5) :
      (R z).val.val.rep i / (R z).val.val.rep j = S i z / S j z := by
    obtain ⟨hv, h⟩ := hR z
    rw [h]
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (fun j => S j z) hv
    rw [← ha]
    exact mul_div_mul_left _ _ a.ne_zero
  have hfactor (c : Fin 2) (z : ℂ) (hz : S (extensionChartDenominator c) z ≠ 0) :
      F z = S (extensionChartDenominator c) z ^ n * f c z := by
    have hval := ((hnorm.2 m n Q hQ c 0).2 z hz).1
    simp only [iteratedDeriv_zero, Function.iterate_zero_apply, hratio] at hval
    have hcancel (j : Fin 5) : S (extensionChartDenominator c) z *
        (S j z / S (extensionChartDenominator c) z) = S j z := by
      field_simp
    have hs := projective_block_scaling n Q (fun d hd => (hQ d hd).2) z
      (S (extensionChartDenominator c) z) (fun j => S j z / S (extensionChartDenominator c) z)
    simpa only [hcancel, hval] using hs
  have horder (c : Fin 2) (z : ℂ) (hz : S (extensionChartDenominator c) z ≠ 0) :
      analyticOrderAt F z = analyticOrderAt (f c) z := by
    have hU : IsOpen {w : ℂ | S (extensionChartDenominator c) w ≠ 0} :=
      (hS _).continuous.isOpen_preimage _ isOpen_ne
    have heq : F =ᶠ[𝓝 z] (fun w => S (extensionChartDenominator c) w ^ n * f c w) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact hfactor c w hw
    rw [analyticOrderAt_congr heq]
    change analyticOrderAt ((S (extensionChartDenominator c)) ^ n * f c) z = _
    have hunit : analyticOrderAt (S (extensionChartDenominator c) ^ n) z = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (pow_ne_zero n hz))
    rw [analyticOrderAt_mul
      ((hS (extensionChartDenominator c) z (Set.mem_univ _)).pow n) (hfa c z hz),
      hunit, zero_add]
  choose N hNpos hNtest using fun c : Fin 2 => finite_polynomial_zero_test
    (fun k => (extensionChartDerivation g₂ g₃ c)^[k] (extensionChartNormalize c Q))
  let M := max (N 0) (N 1)
  have hNM (c : Fin 2) : N c ≤ M := by
    fin_cases c <;> simp [M]
  have hdetect (c : Fin 2) (z : ℂ) (hz : S (extensionChartDenominator c) z ≠ 0) :
      ∃ k < M, eval (extensionChartCoordinates S c z)
        ((extensionChartDerivation g₂ g₃ c)^[k] (extensionChartNormalize c Q)) ≠ 0 := by
    by_contra! hall
    have hzero := hNtest c (extensionChartCoordinates S c z)
      (fun k hk => hall k (lt_of_lt_of_le hk (hNM c)))
    have htop : analyticOrderAt (f c) z = ⊤ := by
      apply ENat.eq_top_iff_forall_ge.mpr
      intro k
      exact ((hjets c _ k).2 z hz).2.mpr (fun l _ => hzero l)
    exact hnonzero ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hFa).mp
      ((horder c z hz).trans htop))
  refine ⟨M, lt_of_lt_of_le (hNpos 0) (hNM 0), ?_, hdetect⟩
  intro z
  have hcover : ∃ c : Fin 2, S (extensionChartDenominator c) z ≠ 0 := by
    rcases (R z).property with h0 | h2
    · exact ⟨0, (hnorm.1 z 0).mp h0⟩
    · exact ⟨1, (hnorm.1 z 2).mp h2⟩
  obtain ⟨c, hc⟩ := hcover
  obtain ⟨k, hk, hne⟩ := hdetect c z hc
  change analyticOrderAt F z < (M : ℕ∞)
  rw [horder c z hc]
  apply lt_of_not_ge
  intro hle
  exact hne (((hjets c _ M).2 z hc).2.mp hle k hk)

