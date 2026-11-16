-- Prove2me | solution 1 for RGMISFast.lemma_5_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T00:03:45.027539+00:00
-- url     : https://prove2.me/submissions/7106fc92-c0fa-41b8-a391-a90f52dcd0ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RGMISFast_Ncount_measurable
import Theorems.Thm_RGMISFast_root_count_expectation_drift
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

set_option autoImplicit false
namespace PrescribedDecay

open Set

/-- The negative inverse power converts the nonlinear differential inequality
into a lower bound on its derivative. -/
theorem inverse_power_derivative_lower (y v c : ℝ) (k : ℕ)
    (hy : 0 < y) (hk : 0 < k)
    (hv : v ≤ -(k : ℝ) * c * y ^ (1 + (k : ℝ)⁻¹)) :
    c ≤ v * (-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hcoeff : (-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr hkpos.le))
      (Real.rpow_nonneg hy.le _)
  have hmul := mul_le_mul_of_nonpos_right hv hcoeff
  have hidentity : (-(k : ℝ) * c * y ^ (1 + (k : ℝ)⁻¹)) *
      ((-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1)) = c := by
    calc
      _ = (k : ℝ) * (k : ℝ)⁻¹ * c *
          (y ^ (1 + (k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1)) := by ring
      _ = c := by
        rw [← Real.rpow_add hy]
        have hexp : (1 + (k : ℝ)⁻¹) + (-(k : ℝ)⁻¹ - 1) = 0 := by ring
        rw [hexp, Real.rpow_zero, mul_inv_cancel₀ hkpos.ne']
        ring
  rw [hidentity] at hmul
  nlinarith [hmul]

/-- Integration with an arbitrary differentiable clock. This stronger form
retains the initial value and requires strict positivity of the function. -/
theorem inverse_power_clock_growth
    (f f' q q' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hfcont : ContinuousOn f (Icc 0 a)) (hqcont : ContinuousOn q (Icc 0 a))
    (hfpos : ∀ t ∈ Icc 0 a, 0 < f t)
    (hfderiv : ∀ t ∈ Ioo 0 a, HasDerivAt f (f' t) t)
    (hqderiv : ∀ t ∈ Ioo 0 a, HasDerivAt q (q' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      f' t ≤ -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹)) :
    f 0 ^ (-(k : ℝ)⁻¹) + (q a - q 0) ≤ f a ^ (-(k : ℝ)⁻¹) := by
  let F : ℝ → ℝ := fun t ↦ f t ^ (-(k : ℝ)⁻¹) - q t
  have hFcont : ContinuousOn F (Icc 0 a) :=
    (hfcont.rpow_const (fun t ht ↦ Or.inl (hfpos t ht).ne')).sub hqcont
  have hFderiv (t : ℝ) (ht : t ∈ Ioo 0 a) :
      HasDerivAt F
        (f' t * (-(k : ℝ)⁻¹) * f t ^ (-(k : ℝ)⁻¹ - 1) - q' t) t :=
    ((hfderiv t ht).rpow_const (Or.inl (hfpos t ⟨ht.1.le, ht.2.le⟩).ne')).sub
      (hqderiv t ht)
  have hmono : MonotoneOn F (Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a) hFcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hFderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hFderiv t ht).deriv]
      have h := inverse_power_derivative_lower (f t) (f' t) (q' t) k
        (hfpos t ⟨ht.1.le, ht.2.le⟩) hk (hode t ht)
      linarith
  have hends := hmono (show (0 : ℝ) ∈ Icc 0 a from ⟨le_rfl, ha.le⟩)
    (show a ∈ Icc 0 a from ⟨ha.le, le_rfl⟩) ha.le
  dsimp [F] at hends
  linarith

/-- Turning a lower bound on a negative inverse power back into an ordinary
power upper bound. -/
theorem le_inverse_pow_of_inverse_power_lower (y L : ℝ) (k : ℕ)
    (hy : 0 < y) (hL : 0 < L) (hk : 0 < k)
    (h : L ≤ y ^ (-(k : ℝ)⁻¹)) :
    y ≤ (L⁻¹) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh := Real.rpow_le_rpow_of_nonpos hL h (neg_nonpos.mpr hkpos.le)
  rw [← Real.rpow_mul hy.le] at hh
  have hexp : (-(k : ℝ)⁻¹) * (-(k : ℝ)) = 1 := by field_simp
  rw [hexp, Real.rpow_one, Real.rpow_neg hL.le, Real.rpow_natCast, ← inv_pow] at hh
  exact hh

/-- The nonnegative version needs no strict positivity assumption: the ODE
makes `f` nonincreasing, so either the endpoint is zero or the whole interval
has positive values and the inverse-power argument applies. -/
theorem power_decay_bound_with_clock
    (f f' q q' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hfcont : ContinuousOn f (Icc 0 a)) (hqcont : ContinuousOn q (Icc 0 a))
    (hfnonneg : ∀ t ∈ Icc 0 a, 0 ≤ f t)
    (hqnonneg : ∀ t ∈ Ioo 0 a, 0 ≤ q' t)
    (hfderiv : ∀ t ∈ Ioo 0 a, HasDerivAt f (f' t) t)
    (hqderiv : ∀ t ∈ Ioo 0 a, HasDerivAt q (q' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      f' t ≤ -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹))
    (hclock : 0 < q a - q 0) :
    f a ≤ ((q a - q 0)⁻¹) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hazero : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  have haend : a ∈ Icc 0 a := ⟨ha.le, le_rfl⟩
  have hanti : AntitoneOn f (Icc 0 a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 a) hfcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hfderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hfderiv t ht).deriv]
      have hnonpos : -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkpos.le) (hqnonneg t ht))
          (Real.rpow_nonneg (hfnonneg t ⟨ht.1.le, ht.2.le⟩) _)
      exact (hode t ht).trans hnonpos
  by_cases hzero : f a = 0
  · rw [hzero]
    exact pow_nonneg (inv_nonneg.mpr hclock.le) _
  · have hfapos : 0 < f a := lt_of_le_of_ne (hfnonneg a haend) (Ne.symm hzero)
    have hfpos : ∀ t ∈ Icc 0 a, 0 < f t := by
      intro t ht
      exact hfapos.trans_le (hanti ht haend ht.2)
    have hgrowth := inverse_power_clock_growth f f' q q' a k ha hk
      hfcont hqcont hfpos hfderiv hqderiv hode
    have hlow : q a - q 0 ≤ f a ^ (-(k : ℝ)⁻¹) := by
      have hinit := Real.rpow_nonneg (hfnonneg 0 hazero) (-(k : ℝ)⁻¹)
      linarith
    exact le_inverse_pow_of_inverse_power_lower (f a) (q a - q 0) k
      hfapos hclock hk hlow

/-- The autonomous version after the time change `s = -log (1-t)`. -/
theorem power_decay_bound
    (g g' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hgcont : ContinuousOn g (Icc 0 a))
    (hgnonneg : ∀ t ∈ Icc 0 a, 0 ≤ g t)
    (hgderiv : ∀ t ∈ Ioo 0 a, HasDerivAt g (g' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      g' t ≤ -(k : ℝ) / Real.exp 1 * g t ^ (1 + (k : ℝ)⁻¹)) :
    g a ≤ (Real.exp 1 / a) ^ k := by
  have h := power_decay_bound_with_clock g g' (fun t ↦ t / Real.exp 1)
    (fun _ ↦ 1 / Real.exp 1) a k ha hk hgcont
    (continuous_id.div_const _).continuousOn hgnonneg
    (fun _ _ ↦ by positivity) hgderiv
    (fun t _ ↦ (hasDerivAt_id t).div_const (Real.exp 1))
    (fun t ht ↦ by simpa only [div_eq_mul_inv, one_mul] using hode t ht)
    (by simp only [zero_div, sub_zero]; positivity)
  simpa only [zero_div, sub_zero, inv_div] using h


end PrescribedDecay
open RGMISFast
set_option autoImplicit false

lemma singleton_attached_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u : V) (W : Finset V) :
    IsAttached G {u} W ↔ u ∉ W ∧ IsRootConnected G u (insert u W) := by
  classical
  constructor
  · rintro ⟨hd,hr⟩
    have hu : u ∉ W := by simpa using hd
    refine ⟨hu,Finset.mem_insert_self _ _,?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hx
    · subst x
      exact .refl _
    · obtain ⟨y,hy,hyx⟩ := hr x hx
      have he : y = u := Finset.mem_singleton.mp hy
      subst y
      simpa using hyx
  · rintro ⟨hu,hroot⟩
    refine ⟨by simpa using hu,?_⟩
    intro w hw
    exact ⟨u,Finset.mem_singleton_self _,by simpa using hroot.2 w (Finset.mem_insert_of_mem hw)⟩

lemma Y_eq_Ncount_singleton {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) (r : V → ℝ) :
    Y G u k t r = Ncount G {u} k t r := by
  classical
  unfold Y Ncount
  symm
  apply Finset.card_bij (fun W _ => insert u W)
  · intro W hW
    obtain ⟨_,hc,ha,ht⟩ := Finset.mem_filter.mp hW
    obtain ⟨hu,hr⟩ := (singleton_attached_iff G u W).mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hr,?_,by simpa using ht⟩
    rw [Finset.card_insert_of_notMem hu,hc]
  · intro W hW Z hZ he
    have huW := ((singleton_attached_iff G u W).mp (Finset.mem_filter.mp hW).2.2.1).1
    have huZ := ((singleton_attached_iff G u Z).mp (Finset.mem_filter.mp hZ).2.2.1).1
    have hh := congrArg (fun A : Finset V => A.erase u) he
    simpa [Finset.erase_insert,Finset.erase_eq_of_notMem huW,Finset.erase_eq_of_notMem huZ] using hh
  · intro B hB
    obtain ⟨_,hr,hcard,ht⟩ := Finset.mem_filter.mp hB
    have he : insert u (B.erase u) = B := Finset.insert_erase hr.1
    refine ⟨B.erase u,?_,he⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_,?_⟩
    · rw [Finset.card_erase_of_mem hr.1,hcard]
      omega
    · apply (singleton_attached_iff G u _).mpr
      exact ⟨Finset.notMem_erase _ _,by simpa only [he] using hr⟩
    · simpa [he] using ht
lemma l52_Ncount_zero_le_one {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (t : ℝ) (r : V → ℝ) :
    Ncount G A 0 t r ≤ 1 := by
  classical
  unfold Ncount
  have hsub : (Finset.univ.filter (fun W : Finset V => W.card = 0 ∧
      IsAttached G A W ∧ ActiveAt G r t (A ∪ W))) ⊆ {∅} := by
    intro W hW
    exact Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (Finset.mem_filter.mp hW).2.1)
  simpa using Finset.card_le_card hsub



lemma Y_zero_integral {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (t : ℝ) :
    ∫⁻ r, (Y G u 0 t r : ℝ≥0∞) ∂(rankLaw V) ≤ 1 := by
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure (by norm_num)
  have : IsProbabilityMeasure (rankLaw V) := by unfold rankLaw; infer_instance
  calc
    _ ≤ ∫⁻ r : V → ℝ, (1:ℝ≥0∞) ∂(rankLaw V) := by
      apply lintegral_mono
      intro r
      change (Y G u 0 t r : ℝ≥0∞) ≤ 1
      rw [Y_eq_Ncount_singleton]
      exact_mod_cast l52_Ncount_zero_le_one G {u} t r
    _ = 1 := by simp

theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    Measurable (fun r : V → ℝ => Y G u k t r) ∧
    ∫⁻ r, (Y G u k t r : ℝ≥0∞) ∂(rankLaw V) ≤ ENNReal.ofReal ((Real.exp 1 / t) ^ k) := by
  constructor
  · simpa only [Y_eq_Ncount_singleton] using Ncount_measurable G {u} k t
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using Y_zero_integral G u t
    · obtain ⟨f,f',hrep,hcont,hnonneg,hderiv,hode⟩ :=
        root_count_expectation_drift G u t ht k hk
      have hb := PrescribedDecay.power_decay_bound f f' t k ht hk hcont hnonneg hderiv hode
      rw [hrep t ⟨ht.le,le_rfl⟩]
      exact ENNReal.ofReal_le_ofReal hb


