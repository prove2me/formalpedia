-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_chart_canonical_base
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T20:35:38.428744+00:00
-- url     : https://prove2.me/submissions/24e0f2ce-666c-41ad-a10e-48f06aaa791d

import Definitions.Def_WeierstrassEllipticZeta_ChartOrbitBase
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_analytic_orbit
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Tactic

noncomputable section
open Filter
open scoped Topology
namespace TranscendenceTheory

private lemma mem_orbit_kernel_iff {R : Type*} [CommRing R]
    (φ : R →+* (ℂ → ℂ)) (z : ℂ) (r : R) :
    r ∈ analyticOrbitKernel φ z ↔ analyticOrderAt (φ r) z = ⊤ := by
  change (φ r : Germ (𝓝 z) ℂ) = 0 ↔ _
  rw [analyticOrderAt_eq_top]
  exact Germ.coe_eq

private lemma orbit_iterate_eq {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (D : Derivation K R R) (φ : R →+* (ℂ → ℂ)) (z : ℂ)
    (hD : ∀ r, φ (D r) =ᶠ[𝓝 z] deriv (φ r)) (f : R) (n : ℕ) :
    φ ((D^[n]) f) =ᶠ[𝓝 z] iteratedDeriv n (φ f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', iteratedDeriv_succ]
    exact (hD _).trans ih.deriv

/-- An analytic orbit with a nonzero relation supplies a canonical base ideal
of height at least two and the required terminal derivative containment. -/
theorem analytic_orbit_base_height_and_contact
    (K R : Type*) [CommRing K] [CommRing R] [IsDomain R] [Algebra K R]
    (D : Derivation K R R) (φ : R →+* (ℂ → ℂ)) (z : ℂ)
    (ha : ∀ r, AnalyticAt ℂ (φ r) z)
    (hD : ∀ r, φ (D r) =ᶠ[𝓝 z] deriv (φ r))
    (g : R) (hg : g ≠ 0) (hgerm : ∀ᶠ w in 𝓝 z, φ g w = 0)
    (f : R) (hfinite : analyticOrderAt (φ f) z ≠ ⊤)
    (T : ℕ) (horder : ((T + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (φ f) z) :
    (analyticOrbitKernel φ z).IsPrime ∧
      (2 : ℕ∞) ≤ (analyticOrbitBaseIdeal φ z f).height ∧
      f ∈ analyticOrbitBaseIdeal φ z f ∧
      ∀ r ∈ differentialProlongation D (analyticOrbitBaseIdeal φ z f) T, φ r z = 0 := by
  classical
  let p := analyticOrbitKernel φ z
  have hp : p.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro heq
      have hone : (1 : R) ∈ p := by rw [heq]; trivial
      have h := analyticOrderAt_eq_top.mp ((mem_orbit_kernel_iff φ z 1).mp hone)
      have hz := h.self_of_nhds
      simp at hz
    · intro a b hab
      have h := (mem_orbit_kernel_iff φ z (a * b)).mp hab
      rw [map_mul, analyticOrderAt_mul (ha a) (ha b), ENat.add_eq_top] at h
      exact h.imp ((mem_orbit_kernel_iff φ z a).mpr) ((mem_orbit_kernel_iff φ z b).mpr)
  let : p.IsPrime := hp
  have hgp : g ∈ p := (mem_orbit_kernel_iff φ z g).mpr (analyticOrderAt_eq_top.mpr hgerm)
  have hp0 : (⊥ : Ideal R) < p := bot_lt_iff_ne_bot.mpr (by
    intro heq
    exact hg (Ideal.mem_bot.mp (heq ▸ hgp)))
  have hpheight : (1 : ℕ∞) ≤ p.height := calc
    (1 : ℕ∞) ≤ (⊥ : Ideal R).height + 1 := by simp
    _ ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hp0
  have hfnot : f ∉ p := fun h => hfinite ((mem_orbit_kernel_iff φ z f).mp h)
  have hfmem : f ∈ analyticOrbitBaseIdeal φ z f :=
    (show Ideal.span ({f} : Set R) ≤ analyticOrbitBaseIdeal φ z f from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton f))
  have hheight : (2 : ℕ∞) ≤ (analyticOrbitBaseIdeal φ z f).height := by
    rw [Ideal.height_eq_inf_minimalPrimes]
    refine le_iInf₂ (fun q hq => ?_)
    let : q.IsPrime := hq.isPrime
    have hpq : p ≤ q := le_sup_left.trans hq.le
    have hlt : p < q := lt_of_le_of_ne hpq (by
      intro heq
      exact hfnot (heq ▸ hq.le hfmem))
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p.height + 1 := by gcongr
      _ ≤ q.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  let jets : Ideal R := {
    carrier := {r | ((T + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (φ r) z}
    zero_mem' := by
      change ((T + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (φ 0) z
      rw [map_zero, analyticOrderAt_eq_top.mpr (by simp)]
      exact le_top
    add_mem' := by
      intro a b ha hb
      change ((T + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (φ (a + b)) z
      simpa only [map_add] using (le_min ha hb).trans le_analyticOrderAt_add
    smul_mem' := by
      intro a b hb
      change ((T + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (φ (a * b)) z
      rw [map_mul, analyticOrderAt_mul (ha a) (ha b)]
      exact hb.trans (le_add_left le_rfl)
  }
  have hbase : analyticOrbitBaseIdeal φ z f ≤ jets := by
    apply sup_le
    · intro r hr
      change ((T + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (φ r) z
      rw [(mem_orbit_kernel_iff φ z r).mp hr]
      exact le_top
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr horder)
  refine ⟨hp, hheight, hfmem, ?_⟩
  have hvanish : differentialProlongation D (analyticOrbitBaseIdeal φ z f) T ≤
      RingHom.ker ((Pi.evalRingHom (fun _ : ℂ => ℂ) z).comp φ) := by
    apply Ideal.span_le.mpr
    rintro r ⟨a, ha', k, hk, rfl⟩
    change φ ((D^[k]) a) z = 0
    rw [(orbit_iterate_eq D φ z hD a k).self_of_nhds]
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha a)).mp
      (hbase ha') k (Nat.lt_succ_of_le hk)
  exact fun r hr => hvanish hr

end TranscendenceTheory

noncomputable section
open MvPolynomial Filter
open scoped Topology
namespace WeierstrassEllipticZeta

private lemma normalization_eval (c : Fin 2) (t : ℂ) (v : Fin 5 → ℂ)
    (hquad : v 0 * v 4 - v 2 * v 3 - 2 * v 1 ^ 2 = 0)
    (hv : v (extensionChartDenominator c) ≠ 0) (Q : MvPolynomial (Fin 7) ℂ) :
    eval (extensionChartCoordinates (fun j _ => v j) c t) (extensionChartNormalize c Q) =
      eval ![1, t, v 0 / v (extensionChartDenominator c),
        v 1 / v (extensionChartDenominator c), v 2 / v (extensionChartDenominator c),
        v 3 / v (extensionChartDenominator c), v 4 / v (extensionChartDenominator c)] Q := by
  have heval (f : Fin 4 → ℂ) :
      eval f (extensionChartNormalize c Q) =
        eval (fun i => eval f (extensionChartSubstitution c i)) Q := by
    exact comp_aeval_apply (extensionChartSubstitution c) (aeval f) Q
  rw [heval]
  apply congrArg (fun f : Fin 7 → ℂ => eval f Q)
  funext i
  fin_cases c
  · have hv0 : v 0 ≠ 0 := hv
    have hlast : v 2 / v 0 * (v 3 / v 0) + 2 * (v 1 / v 0) ^ 2 = v 4 / v 0 := by
      field_simp
      linear_combination -hquad
    fin_cases i <;> simp [extensionChartSubstitution, extensionChartCoordinates,
      extensionChartDenominator, hv0, hlast]
  · have hv2 : v 2 ≠ 0 := hv
    have hthird : v 0 / v 2 * (v 4 / v 2) - 2 * (v 1 / v 2) ^ 2 = v 3 / v 2 := by
      field_simp
      linear_combination hquad
    fin_cases i <;> simp [extensionChartSubstitution, extensionChartCoordinates,
      extensionChartDenominator, hv2, hthird]

private lemma chart_cubic_ne_zero (g₂ g₃ : ℂ) (c : Fin 2) :
    extensionChartCubic g₂ g₃ c ≠ 0 := by
  intro h
  fin_cases c
  · have h0 := congrArg (eval (![0, 0, 0, 0] : Fin 4 → ℂ)) h
    have h1 := congrArg (eval (![0, 0, 1, 0] : Fin 4 → ℂ)) h
    simp [extensionChartCubic] at h0 h1
    simp [h0] at h1
  · have h1 := congrArg (eval (fun i : Fin 4 => if i = 2 then (1 : ℂ) else 0)) h
    norm_num [extensionChartCubic, show (1 : Fin 4) ≠ 2 by decide] at h1

private lemma coordinate_relations
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    (∀ w, S 0 w * S 4 w - S 2 w * S 3 w - 2 * S 1 w ^ 2 = 0) ∧
    (∀ w, S 2 w ^ 2 * S 0 w - 4 * S 1 w ^ 3 +
      L.g₂ * S 1 w * S 0 w ^ 2 + L.g₃ * S 0 w ^ 3 = 0) := by
  have ha (j : Fin 5) (w : ℂ) : AnalyticAt ℂ (S j) w := hS j w trivial
  constructor
  · have heq : (fun w => S 0 w * S 4 w - S 2 w * S 3 w - 2 * S 1 w ^ 2) =
        (0 : ℂ → ℂ) := by
      apply AnalyticOnNhd.eq_of_eventuallyEq
        (show AnalyticOnNhd ℂ _ Set.univ from fun w _ => by fun_prop)
        (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
        (z₀ := L.ω₁ / 2)
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
        L.ω₁_div_two_notMem_lattice] with u hu
      simp [hS_value u hu]
      ring
    intro w
    exact congrFun heq w
  · have heq : (fun w => S 2 w ^ 2 * S 0 w - 4 * S 1 w ^ 3 +
        L.g₂ * S 1 w * S 0 w ^ 2 + L.g₃ * S 0 w ^ 3) = (0 : ℂ → ℂ) := by
      apply AnalyticOnNhd.eq_of_eventuallyEq
        (show AnalyticOnNhd ℂ _ Set.univ from fun w _ => by fun_prop)
        (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
        (z₀ := L.ω₁ / 2)
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
        L.ω₁_div_two_notMem_lattice] with u hu
      have hc := L.derivWeierstrassP_sq u hu
      simp [hS_value u hu]
      linear_combination D.sigma u ^ 9 * hc
    intro w
    exact congrFun heq w


end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun w : ℂ => eval
      ![1, w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q) ≠ 0)
    (c : Fin 2) (z : ℂ) (hz : S (extensionChartDenominator c) z ≠ 0)
    (T : ℕ)
    (horder : ((T + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
      (fun w : ℂ => eval ![1, w, S 0 w / S (extensionChartDenominator c) w,
        S 1 w / S (extensionChartDenominator c) w,
        S 2 w / S (extensionChartDenominator c) w,
        S 3 w / S (extensionChartDenominator c) w,
        S 4 w / S (extensionChartDenominator c) w] Q) z) :
    (2 : ℕ∞) ≤ (extensionChartBaseIdeal S Q c z).height ∧
      extensionChartNormalize c Q ∈ extensionChartBaseIdeal S Q c z ∧
      TranscendenceTheory.differentialProlongation (extensionChartDerivation L.g₂ L.g₃ c)
        (extensionChartBaseIdeal S Q c z) T ≤
          RingHom.ker (eval (extensionChartCoordinates S c z)) := by
  classical
  obtain ⟨φ, hφ, hD, _, hfinite⟩ := elliptic_chart_analytic_orbit
    L D S hS hS_value Q n hQ hne c z hz
  have hφeq : φ.toRingHom = extensionChartEvalHom S c := by
    apply RingHom.ext
    intro r
    funext w
    exact hφ r w
  have hcompat (r : MvPolynomial (Fin 4) ℂ) :
      extensionChartEvalHom S c (extensionChartDerivation L.g₂ L.g₃ c r)
        =ᶠ[𝓝 z] deriv (extensionChartEvalHom S c r) := by
    rw [← hφeq]
    change φ ((extensionChartDerivation L.g₂ L.g₃ c).restrictScalars ℚ r)
      =ᶠ[𝓝 z] deriv (φ r)
    exact hD r
  have ha (r : MvPolynomial (Fin 4) ℂ) :
      AnalyticAt ℂ (extensionChartEvalHom S c r) z := by
    apply AnalyticAt.aeval_mvPolynomial
    intro i
    fin_cases c <;> fin_cases i <;> simp [extensionChartCoordinates]
    all_goals first | exact analyticAt_id |
      exact (hS _ z trivial).div (hS _ z trivial) hz
  obtain ⟨hquad, hcubic⟩ := coordinate_relations L D S hS hS_value
  have hU : IsOpen {w : ℂ | S (extensionChartDenominator c) w ≠ 0} :=
    (hS _).continuous.isOpen_preimage _ isOpen_ne
  have hrelation : ∀ᶠ w in 𝓝 z,
      extensionChartEvalHom S c (extensionChartCubic L.g₂ L.g₃ c) w = 0 := by
    filter_upwards [hU.mem_nhds hz] with w hw
    change eval (extensionChartCoordinates S c w) (extensionChartCubic L.g₂ L.g₃ c) = 0
    have hc := hcubic w
    fin_cases c <;> simp [extensionChartDenominator] at hw
    · simp [extensionChartCoordinates, extensionChartCubic]
      field_simp
      linear_combination hc
    · simp [extensionChartCoordinates, extensionChartCubic]
      field_simp
      linear_combination hc
  have hnorm : (fun w : ℂ => eval ![1, w, S 0 w / S (extensionChartDenominator c) w,
        S 1 w / S (extensionChartDenominator c) w,
        S 2 w / S (extensionChartDenominator c) w,
        S 3 w / S (extensionChartDenominator c) w,
        S 4 w / S (extensionChartDenominator c) w] Q)
      =ᶠ[𝓝 z] extensionChartEvalHom S c (extensionChartNormalize c Q) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (normalization_eval c w (fun j => S j w) (hquad w) hw Q).symm
  have horder' : ((T + 1 : ℕ) : ℕ∞) ≤
      analyticOrderAt (extensionChartEvalHom S c (extensionChartNormalize c Q)) z := by
    rwa [analyticOrderAt_congr hnorm] at horder
  have H := TranscendenceTheory.analytic_orbit_base_height_and_contact
    ℂ (MvPolynomial (Fin 4) ℂ) (extensionChartDerivation L.g₂ L.g₃ c)
    (extensionChartEvalHom S c) z ha hcompat
    (extensionChartCubic L.g₂ L.g₃ c) (chart_cubic_ne_zero L.g₂ L.g₃ c) hrelation
    (extensionChartNormalize c Q) (by
      rw [← hφeq]
      change analyticOrderAt (φ (extensionChartNormalize c Q)) z ≠ ⊤
      exact hfinite) T horder'
  exact ⟨H.2.1, H.2.2.1, fun r hr => H.2.2.2 r hr⟩
