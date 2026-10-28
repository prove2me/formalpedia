-- Prove2me | solution 1 for RiskyBenefitCost.NthDegree.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T08:37:42.334561+00:00
-- url     : https://prove2.me/submissions/de79c7c0-a1f6-42bf-a011-f8824104794d

import Mathlib
import Definitions.Def_RiskyBenefitCost_NthDegree_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace RBCP2

open RiskyBenefitCost.NthDegree

/-- Regularity of the iterated CDFs. -/
lemma iterCDF_reg (μ : Measure ℝ) [IsProbabilityMeasure μ] (xl : ℝ) (k : ℕ) :
    Measurable (iterCDF μ xl k) ∧ (∀ a b, IntervalIntegrable (iterCDF μ xl k) volume a b) ∧
      (∀ x, ContinuousWithinAt (iterCDF μ xl k) (Ici x) x) := by
  induction k with
  | zero =>
    have hm : Monotone (iterCDF μ xl 0) := by
      show Monotone (fun z => cdf μ z)
      exact monotone_cdf μ
    refine ⟨hm.measurable, fun a b => hm.intervalIntegrable, fun x => ?_⟩
    show ContinuousWithinAt (fun z => cdf μ z) (Ici x) x
    exact (cdf μ).right_continuous x
  | succ k ih =>
    have hc : Continuous (iterCDF μ xl (k + 1)) := by
      show Continuous (fun z => ∫ t in xl..z, iterCDF μ xl k t)
      exact intervalIntegral.continuous_primitive ih.2.1 xl
    exact ⟨hc.measurable, fun a b => hc.intervalIntegrable a b,
      fun x => hc.continuousWithinAt⟩

lemma iterCDF_succ_self (μ : Measure ℝ) (xl : ℝ) (k : ℕ) : iterCDF μ xl (k + 1) xl = 0 := by
  show (∫ t in xl..xl, iterCDF μ xl k t) = 0
  simp

/-- One integration-by-parts step. -/
lemma ibp_step (μ : Measure ℝ) [IsProbabilityMeasure μ] (xl xu : ℝ) (k : ℕ)
    (ψ ψ' : ℝ → ℝ) (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (hψ' : Continuous ψ') :
    ∫ x in xl..xu, ψ x * iterCDF μ xl k x =
      ψ xu * iterCDF μ xl (k + 1) xu - ∫ x in xl..xu, ψ' x * iterCDF μ xl (k + 1) x := by
  obtain ⟨hmeas, hint, hrc⟩ := iterCDF_reg μ xl k
  have hv : Continuous (iterCDF μ xl (k + 1)) := by
    show Continuous (fun z => ∫ t in xl..z, iterCDF μ xl k t)
    exact intervalIntegral.continuous_primitive hint xl
  have hu : Continuous ψ := continuous_iff_continuousAt.2 fun x => (hψ x).continuousAt
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := ψ) (v := iterCDF μ xl (k + 1)) (u' := ψ') (v' := iterCDF μ xl k) (a := xl) (b := xu)
    hu.continuousOn hv.continuousOn (fun x _ => (hψ x).hasDerivWithinAt)
    (fun x _ => by
      have h1 : HasDerivWithinAt (fun u => ∫ t in xl..u, iterCDF μ xl k t)
          (iterCDF μ xl k x) (Ici x) x :=
        intervalIntegral.integral_hasDerivWithinAt_right (hint xl x)
          hmeas.stronglyMeasurable.stronglyMeasurableAtFilter
          ((hrc x).mono Ioi_subset_Ici_self)
      exact h1.mono Ioi_subset_Ici_self)
    (hψ'.intervalIntegrable _ _) (hint xl xu)
  rw [key, iterCDF_succ_self]
  ring

/-- Base step: `∫ φ dμ = φ xu - ∫_{xl}^{xu} φ' F`. -/
lemma ibp_base (μ : Measure ℝ) [IsProbabilityMeasure μ] (xl xu : ℝ) (hle : xl ≤ xu)
    (hμ : μ (Icc xl xu)ᶜ = 0) (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : Continuous φ') :
    ∫ X, φ X ∂μ = φ xu - ∫ x in xl..xu, φ' x * cdf μ x := by
  set F : ℝ → ℝ → ℝ := fun X x => if x < X then φ' x else 0 with hFdef
  have hX : ∀ X ∈ Icc xl xu, φ X = φ xl + ∫ x in Ioc xl xu, F X x := by
    intro X hX
    have h1 : ∫ x in xl..X, φ' x = φ X - φ xl :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hφ x)
        (hφ'.intervalIntegrable _ _)
    have h2 : ∫ x in Ioc xl xu, F X x = ∫ x in Ioo xl X, φ' x := by
      have : (fun x => F X x) = (Iio X).indicator φ' := by
        funext x; simp only [hFdef, Set.indicator, mem_Iio]
      rw [this, setIntegral_indicator measurableSet_Iio]
      have hs : Ioc xl xu ∩ Iio X = Ioo xl X := by
        ext y; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]; constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith [hX.2]⟩, h3⟩
      rw [hs]
    rw [h2, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hX.1, h1]; ring
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := xl) (b := xu)).exists_bound_of_continuousOn
    hφ'.continuousOn
  have hFint : Integrable (Function.uncurry F) (μ.prod (volume.restrict (Ioc xl xu))) := by
    refine Integrable.of_bound ?_ C ?_
    · have : Measurable (Function.uncurry F) := by
        show Measurable (fun p : ℝ × ℝ => if p.2 < p.1 then φ' p.2 else 0)
        exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
          (hφ'.measurable.comp measurable_snd) measurable_const
      exact this.aestronglyMeasurable
    · have hs : MeasurableSet (univ ×ˢ Ioc xl xu : Set (ℝ × ℝ)) :=
        MeasurableSet.univ.prod measurableSet_Ioc
      have : ∀ᵐ p ∂(μ.prod (volume.restrict (Ioc xl xu))),
          p ∈ (univ ×ˢ Ioc xl xu : Set (ℝ × ℝ)) := by
        rw [Measure.ae_prod_mem_iff_ae_ae_mem hs]
        exact Filter.Eventually.of_forall fun X =>
          (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ⟨mem_univ _, hx⟩
      filter_upwards [this] with p hp
      show ‖if p.2 < p.1 then φ' p.2 else 0‖ ≤ C
      split_ifs
      · exact hC _ (Ioc_subset_Icc_self hp.2)
      · simpa using (norm_nonneg _).trans (hC xl ⟨le_rfl, hle⟩)
  have hae : ∀ᵐ X ∂μ, X ∈ Icc xl xu := mem_ae_iff.mpr hμ
  have e1 : ∫ X, φ X ∂μ = ∫ X, (φ xl + ∫ x in Ioc xl xu, F X x) ∂μ :=
    integral_congr_ae (hae.mono fun X hXm => hX X hXm)
  have hint1 : Integrable (fun X => ∫ x in Ioc xl xu, F X x) μ := hFint.integral_prod_left
  rw [e1, integral_add (integrable_const _) hint1, integral_const,
    integral_integral_swap hFint]
  have e2 : ∀ x, ∫ X, F X x ∂μ = φ' x * (1 - cdf μ x) := by
    intro x
    have : (fun X => F X x) = (Ioi x).indicator (fun _ => φ' x) := by
      funext X; simp only [hFdef, Set.indicator, mem_Ioi]
    rw [this, integral_indicator measurableSet_Ioi, setIntegral_const, cdf_eq_real,
      ← compl_Iic, measureReal_compl measurableSet_Iic]
    simp; ring
  simp_rw [e2]
  rw [← intervalIntegral.integral_of_le hle]
  simp_rw [mul_sub, mul_one]
  have hcdf : IntervalIntegrable (fun x => φ' x * cdf μ x) volume xl xu :=
    (monotone_cdf μ).intervalIntegrable.continuousOn_mul hφ'.continuousOn
  rw [intervalIntegral.integral_sub (hφ'.intervalIntegrable _ _) hcdf,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hφ x)
      (hφ'.intervalIntegrable _ _)]
  simp; ring

lemma cdf_xu_eq_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (xl xu : ℝ)
    (hμ : μ (Icc xl xu)ᶜ = 0) : cdf μ xu = 1 := by
  have h0 : μ (Iic xu)ᶜ = 0 := measure_mono_null (compl_subset_compl.2 Icc_subset_Iic_self) hμ
  have h1 : μ.real (Iic xu)ᶜ = 0 := by rw [measureReal_def, h0]; rfl
  rw [measureReal_compl measurableSet_Iic] at h1
  have hu : μ.real univ = 1 := by simp
  rw [cdf_eq_real]; linarith

/-- The `n+1`-fold integration by parts formula. -/
lemma ibp_formula (μ : Measure ℝ) [IsProbabilityMeasure μ] (xl xu : ℝ) (hle : xl ≤ xu)
    (hμ : μ (Icc xl xu)ᶜ = 0) (n : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (n + 1) φ) :
    ∫ X, φ X ∂μ = ∑ j ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ j * iteratedDeriv j φ xu * iterCDF μ xl j xu
      + (-1 : ℝ) ^ (n + 1) * ∫ x in xl..xu, iteratedDeriv (n + 1) φ x * iterCDF μ xl n x := by
  induction n with
  | zero =>
    have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hc : Continuous (deriv φ) := hφ.continuous_deriv (by norm_num)
    rw [ibp_base μ xl xu hle hμ φ (deriv φ) (fun x => (hd x).hasDerivAt) hc]
    simp only [zero_add, Finset.sum_range_one, pow_zero, pow_one, iteratedDeriv_zero,
      iteratedDeriv_one, one_mul]
    have : iterCDF μ xl 0 = fun z => cdf μ z := rfl
    rw [this]; beta_reduce; rw [cdf_xu_eq_one μ xl xu hμ]; ring
  | succ n ih =>
    have h1 : ContDiff ℝ (n + 1) φ := hφ.of_le (by norm_cast; omega)
    rw [ih h1]
    have hdiff : Differentiable ℝ (iteratedDeriv (n + 1) φ) :=
      hφ.differentiable_iteratedDeriv (n + 1) (by norm_cast; omega)
    have hcont : Continuous (iteratedDeriv (n + 1 + 1) φ) :=
      hφ.continuous_iteratedDeriv (n + 1 + 1) (by norm_cast)
    have hder : ∀ x, HasDerivAt (iteratedDeriv (n + 1) φ) (iteratedDeriv (n + 1 + 1) φ x) x := by
      intro x
      have := (hdiff x).hasDerivAt
      rwa [← iteratedDeriv_succ] at this
    rw [ibp_step μ xl xu n _ _ hder hcont, Finset.sum_range_succ _ (n + 1)]
    ring

lemma ibp_diff (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (xl xu : ℝ) (hle : xl ≤ xu) (hμ₁ : μ₁ (Icc xl xu)ᶜ = 0) (hμ₂ : μ₂ (Icc xl xu)ᶜ = 0)
    (n : ℕ) (hb : ∀ j ∈ Finset.range (n + 1), iterCDF μ₁ xl j xu = iterCDF μ₂ xl j xu)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (n + 1) φ) :
    ∫ X, φ X ∂μ₂ - ∫ X, φ X ∂μ₁ = (-1 : ℝ) ^ (n + 1) *
      ∫ x in xl..xu, iteratedDeriv (n + 1) φ x * (iterCDF μ₂ xl n x - iterCDF μ₁ xl n x) := by
  rw [ibp_formula μ₂ xl xu hle hμ₂ n φ hφ, ibp_formula μ₁ xl xu hle hμ₁ n φ hφ]
  have hs : ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * iteratedDeriv j φ xu * iterCDF μ₁ xl j xu
      = ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * iteratedDeriv j φ xu * iterCDF μ₂ xl j xu :=
    Finset.sum_congr rfl fun j hj => by rw [hb j hj]
  rw [hs]
  have hc := (hφ.continuous_iteratedDeriv (n + 1) (by norm_cast)).continuousOn (s := uIcc xl xu)
  have i1 := ((iterCDF_reg μ₁ xl n).2.1 xl xu).continuousOn_mul hc
  have i2 := ((iterCDF_reg μ₂ xl n).2.1 xl xu).continuousOn_mul hc
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub i2 i1]
  ring

/-- Sign-adjusted `N`th derivative as a function of `t = f b`. -/
noncomputable def Sfun (n : ℕ) (U : ℝ → ℝ) (x0 z0 t x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * t ^ (n + 1) * iteratedDeriv (n + 1) U (t * (x - x0) + z0)

lemma iter_comp (U : ℝ → ℝ) (M : ℕ) (hU : ContDiff ℝ M U) (t c : ℝ) :
    iteratedDeriv M (fun x => U (t * x + c)) = fun x => t ^ M * iteratedDeriv M U (t * x + c) := by
  have hg : ContDiff ℝ M (fun y => U (y + c)) := hU.comp (contDiff_id.add contDiff_const)
  have h := iteratedDeriv_comp_const_mul hg t
  simp only [iteratedDeriv_comp_add_const] at h
  exact h

lemma D2_eq (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (xl xu : ℝ) (hle : xl ≤ xu) (hμ₁ : μ₁ (Icc xl xu)ᶜ = 0) (hμ₂ : μ₂ (Icc xl xu)ᶜ = 0)
    (n : ℕ) (hb : ∀ j ∈ Finset.range (n + 1), iterCDF μ₁ xl j xu = iterCDF μ₂ xl j xu)
    (U : ℝ → ℝ) (hU : ContDiff ℝ (n + 1) U) (x0 z0 t : ℝ) :
    ∫ X, U (t * (X - x0) + z0) ∂μ₂ - ∫ X, U (t * (X - x0) + z0) ∂μ₁ =
      ∫ x in xl..xu, Sfun n U x0 z0 t x * (iterCDF μ₂ xl n x - iterCDF μ₁ xl n x) := by
  have hφ : ContDiff ℝ (n + 1) (fun X => U (t * (X - x0) + z0)) :=
    hU.comp ((contDiff_const.mul (contDiff_id.sub contDiff_const)).add contDiff_const)
  rw [ibp_diff μ₁ μ₂ xl xu hle hμ₁ hμ₂ n hb _ hφ]
  have hφeq : (fun X => U (t * (X - x0) + z0)) = fun X => U (t * X + (z0 - t * x0)) := by
    funext X; congr 1; ring
  have hU' : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) U := by exact_mod_cast hU
  rw [hφeq, iter_comp U (n + 1) hU' t (z0 - t * x0)]
  have harg : ∀ x, t * x + (z0 - t * x0) = t * (x - x0) + z0 := fun x => by ring
  simp_rw [harg]
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext x; unfold Sfun; ring

lemma S_mono (n : ℕ) (U : ℝ → ℝ) (hU : ContDiff ℝ (n + 1 + 1) U) (D : Set ℝ)
    (hD : D.OrdConnected) (x0 z0 x : ℝ) (hz0 : 0 ≤ z0)
    (hRA_N : ∀ z ∈ D, 0 < (-1 : ℝ) ^ (n + 1 + 1) * iteratedDeriv (n + 1) U z)
    (hRA_N1 : ∀ z ∈ D, 0 ≤ (-1 : ℝ) ^ (n + 1 + 1 + 1) * iteratedDeriv (n + 1 + 1) U z)
    (hrel : ∀ z ∈ D, relRiskAversion (n + 1) U z < ((n + 1 : ℕ) : ℝ))
    (t1 t2 : ℝ) (h12 : t1 ≤ t2) (hz1 : t1 * (x - x0) + z0 ∈ D) (hz2 : t2 * (x - x0) + z0 ∈ D) :
    ((∀ t ∈ Icc t1 t2, 0 ≤ t ^ n) → Sfun n U x0 z0 t2 x ≤ Sfun n U x0 z0 t1 x) ∧
    ((∀ t ∈ Icc t1 t2, t ^ n ≤ 0) → Sfun n U x0 z0 t1 x ≤ Sfun n U x0 z0 t2 x) := by
  have hzD : ∀ t ∈ Icc t1 t2, t * (x - x0) + z0 ∈ D := by
    intro t ht
    apply hD.uIcc_subset hz1 hz2
    rw [mem_uIcc]
    rcases le_total 0 (x - x0) with h | h
    · left; constructor <;> nlinarith [ht.1, ht.2]
    · right; constructor <;> nlinarith [ht.1, ht.2]
  set A := iteratedDeriv (n + 1) U with hAdef
  set A' := iteratedDeriv (n + 1 + 1) U with hA'def
  have hAd : ∀ z, HasDerivAt A (A' z) z := by
    intro z
    have hdiff : Differentiable ℝ (iteratedDeriv (n + 1) U) :=
      hU.differentiable_iteratedDeriv (n + 1) (by norm_cast; omega)
    have := (hdiff z).hasDerivAt
    rwa [← iteratedDeriv_succ] at this
  set Q : ℝ → ℝ := fun t => (-1 : ℝ) ^ (n + 1) *
    (((n + 1 : ℕ) : ℝ) * A (t * (x - x0) + z0) + t * (x - x0) * A' (t * (x - x0) + z0)) with hQdef
  have hderiv : ∀ t, HasDerivAt (fun t => Sfun n U x0 z0 t x) (t ^ n * Q t) t := by
    intro t
    have h1 := ((hasDerivAt_pow (n + 1) t).const_mul ((-1 : ℝ) ^ (n + 1))).mul
      ((hAd (t * (x - x0) + z0)).comp t (((hasDerivAt_id' t).mul_const (x - x0)).add_const z0))
    refine h1.congr_deriv ?_
    simp only [Function.comp_def, Nat.add_sub_cancel, hQdef]
    push_cast; ring
  have hQ : ∀ t ∈ Icc t1 t2, Q t ≤ 0 := by
    intro t ht
    have hz := hzD t ht
    set z := t * (x - x0) + z0 with hz_def
    have hN := hRA_N z hz
    have hN1 := hRA_N1 z hz
    have hr := hrel z hz
    set s : ℝ := (-1 : ℝ) ^ (n + 1) with hs
    have e1 : (-1 : ℝ) ^ (n + 1 + 1) = -s := by rw [pow_succ]; ring
    have e2 : (-1 : ℝ) ^ (n + 1 + 1 + 1) = s := by rw [pow_succ, pow_succ]; ring
    rw [e1] at hN; rw [e2] at hN1
    have hsA : s * A z < 0 := by linarith
    have hA0 : A z ≠ 0 := by intro h; rw [h] at hsA; simp at hsA
    have hrA : relRiskAversion (n + 1) U z * A z = -z * A' z := div_mul_cancel₀ _ hA0
    have key : Q t = s * A z * (((n + 1 : ℕ) : ℝ) - relRiskAversion (n + 1) U z)
        - z0 * (s * A' z) := by
      have hz' : t * (x - x0) + z0 = z := hz_def.symm
      have ht' : t * (x - x0) = z - z0 := by rw [hz_def]; ring
      simp only [hQdef, hz']
      linear_combination s * hrA + s * A' z * ht'
    rw [key]
    nlinarith [mul_neg_of_neg_of_pos hsA (sub_pos.2 hr), mul_nonneg hz0 hN1]
  have hcont : ContinuousOn (fun t => Sfun n U x0 z0 t x) (Icc t1 t2) :=
    fun t _ => (hderiv t).continuousAt.continuousWithinAt
  constructor
  · intro hpow
    have hanti : AntitoneOn (fun t => Sfun n U x0 z0 t x) (Icc t1 t2) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t1 t2) hcont
        (fun t _ => (hderiv t).hasDerivWithinAt)
        (fun t ht => by
          rw [interior_Icc] at ht
          exact mul_nonpos_of_nonneg_of_nonpos (hpow t (Ioo_subset_Icc_self ht))
            (hQ t (Ioo_subset_Icc_self ht)))
    exact hanti ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12
  · intro hpow
    have hmono : MonotoneOn (fun t => Sfun n U x0 z0 t x) (Icc t1 t2) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t1 t2) hcont
        (fun t _ => (hderiv t).hasDerivWithinAt)
        (fun t ht => by
          rw [interior_Icc] at ht
          exact mul_nonneg_of_nonpos_of_nonpos (hpow t (Ioo_subset_Icc_self ht))
            (hQ t (Ioo_subset_Icc_self ht)))
    exact hmono ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12

lemma topkis (B : Set ℝ) (g1 g2 : ℝ → ℝ)
    (h : ∀ b ∈ B, ∀ b' ∈ B, b ≤ b' → g2 b' - g2 b ≤ g1 b' - g1 b) :
    Supermodularity.Lattices.InducedSetOrder (argmaxSet B g2) (argmaxSet B g1) := by
  intro a ha b hb
  rcases le_total a b with hab | hab
  · rw [inf_eq_left.2 hab, sup_eq_right.2 hab]; exact ⟨ha, hb⟩
  · rw [inf_eq_right.2 hab, sup_eq_left.2 hab]
    have h1 := h b hb.1 a ha.1 hab
    have h2 := hb.2 a ha.1
    have h3 := ha.2 b hb.1
    refine ⟨⟨hb.1, fun c hc => ?_⟩, ⟨ha.1, fun c hc => ?_⟩⟩
    · have := ha.2 c hc; linarith
    · have := hb.2 c hc; linarith

end RBCP2

open RBCP2

open RiskyBenefitCost.NthDegree MeasureTheory ProbabilityTheory in
theorem solution (N : ℕ) (hN : 1 ≤ N) (xl xu x0 z0 : ℝ) (hxl : 0 ≤ xl) (hlt : xl < xu)
    (hz0 : 0 ≤ z0)
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : μ₁ (Set.Icc xl xu)ᶜ = 0) (hμ₂ : μ₂ (Set.Icc xl xu)ᶜ = 0)
    (B : Set ℝ) (hB : IsCompact B) (f : ℝ → ℝ) (hf : ContinuousOn f B)
    (U : ℝ → ℝ) (hU : ContDiff ℝ (N + 1) U) (hUmono : Monotone U)
    (D : Set ℝ) (hD : D.OrdConnected)
    (hpay : ∀ b ∈ B, ∀ X ∈ Set.Icc xl xu, f b * (X - x0) + z0 ∈ D)
    (hRA_N : ∀ z ∈ D, 0 < (-1 : ℝ) ^ (N + 1) * iteratedDeriv N U z)
    (hRA_N1 : NthDegreeRiskAverseOn (N + 1) U D)
    (hrel : ∀ z ∈ D, relRiskAversion N U z < N)
    (hinc : IsNthDegreeRiskIncrease N xl xu μ₁ μ₂) :
    (RiskTakingBenefit f B →
      Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₂)) (argmaxSet B (EU U f x0 z0 μ₁))) ∧
    (RiskMitigationBenefit f B →
      Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₁)) (argmaxSet B (EU U f x0 z0 μ₂))) ∧
    (RiskTakingCost f B →
      (Even N → Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₂)) (argmaxSet B (EU U f x0 z0 μ₁))) ∧
      (Odd N → Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₁)) (argmaxSet B (EU U f x0 z0 μ₂)))) ∧
    (RiskMitigationCost f B →
      (Even N → Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₁)) (argmaxSet B (EU U f x0 z0 μ₂))) ∧
      (Odd N → Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₂)) (argmaxSet B (EU U f x0 z0 μ₁)))) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hle : xl ≤ xu := hlt.le
  have hb : ∀ j ∈ Finset.range (n + 1), iterCDF μ₁ xl j xu = iterCDF μ₂ xl j xu := by
    intro j hj
    have := hinc.1 (j + 1) (by simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega)
    simpa using this
  have hW : ∀ x ∈ Icc xl xu, 0 ≤ iterCDF μ₂ xl n x - iterCDF μ₁ xl n x := by
    intro x hx
    have := hinc.2 x hx
    simp only [Nat.add_sub_cancel] at this
    linarith
  have hU1 : ContDiff ℝ (n + 1) U := hU.of_le (by norm_cast; omega)
  have hU2 : ContDiff ℝ (n + 1 + 1) U := by exact_mod_cast hU
  set Dt : ℝ → ℝ := fun t =>
    ∫ x in xl..xu, Sfun n U x0 z0 t x * (iterCDF μ₂ xl n x - iterCDF μ₁ xl n x) with hDt
  have hEU : ∀ b, EU U f x0 z0 μ₂ b - EU U f x0 z0 μ₁ b = Dt (f b) := by
    intro b
    exact D2_eq μ₁ μ₂ xl xu hle hμ₁ hμ₂ n hb U hU1 x0 z0 (f b)
  have hWi : IntervalIntegrable (fun x => iterCDF μ₂ xl n x - iterCDF μ₁ xl n x) volume xl xu :=
    ((iterCDF_reg μ₂ xl n).2.1 xl xu).sub ((iterCDF_reg μ₁ xl n).2.1 xl xu)
  have hSc : ∀ t, Continuous (fun x => Sfun n U x0 z0 t x) := by
    intro t
    have hc := hU1.continuous_iteratedDeriv (n + 1) (by norm_cast)
    unfold Sfun
    exact continuous_const.mul (hc.comp (by fun_prop))
  have hDmono : ∀ t1 t2, (∀ x ∈ Icc xl xu, Sfun n U x0 z0 t1 x ≤ Sfun n U x0 z0 t2 x) →
      Dt t1 ≤ Dt t2 := by
    intro t1 t2 h
    exact intervalIntegral.integral_mono_on hle (hWi.continuousOn_mul (hSc t1).continuousOn)
      (hWi.continuousOn_mul (hSc t2).continuousOn)
      (fun x hx => mul_le_mul_of_nonneg_right (h x hx) (hW x hx))
  have SM := fun b (hb : b ∈ B) b' (hb' : b' ∈ B) (h : f b ≤ f b') x (hx : x ∈ Icc xl xu) =>
    S_mono n U hU2 D hD x0 z0 x hz0 hRA_N hRA_N1 hrel (f b) (f b') h (hpay b hb x hx)
      (hpay b' hb' x hx)
  have caseA : (∀ b ∈ B, ∀ b' ∈ B, b ≤ b' → Dt (f b') ≤ Dt (f b)) →
      Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₂)) (argmaxSet B (EU U f x0 z0 μ₁)) := by
    intro h
    refine topkis B _ _ fun b hb b' hb' hbb => ?_
    have := h b hb b' hb' hbb
    have e1 := hEU b; have e2 := hEU b'
    linarith
  have caseB : (∀ b ∈ B, ∀ b' ∈ B, b ≤ b' → Dt (f b) ≤ Dt (f b')) →
      Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₁)) (argmaxSet B (EU U f x0 z0 μ₂)) := by
    intro h
    refine topkis B _ _ fun b hb b' hb' hbb => ?_
    have := h b hb b' hb' hbb
    have e1 := hEU b; have e2 := hEU b'
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨hmo, hnn⟩
    refine caseA fun b hb b' hb' hbb => hDmono _ _ fun x hx =>
      (SM b hb b' hb' (hmo hb hb' hbb) x hx).1 fun t ht => pow_nonneg ((hnn b hb).trans ht.1) n
  · rintro ⟨hanti, hnn⟩
    refine caseB fun b hb b' hb' hbb => hDmono _ _ fun x hx =>
      (SM b' hb' b hb (hanti hb hb' hbb) x hx).1 fun t ht => pow_nonneg ((hnn b' hb').trans ht.1) n
  · rintro ⟨hanti, hnp⟩
    refine ⟨fun hev => ?_, fun hod => ?_⟩
    · have hn : Odd n := by obtain ⟨k, hk⟩ := hev; exact ⟨k - 1, by omega⟩
      refine caseA fun b hb b' hb' hbb => hDmono _ _ fun x hx =>
        (SM b' hb' b hb (hanti hb hb' hbb) x hx).2 fun t ht =>
          hn.pow_nonpos (ht.2.trans (hnp b hb))
    · have hn : Even n := by obtain ⟨k, hk⟩ := hod; exact ⟨k, by omega⟩
      refine caseB fun b hb b' hb' hbb => hDmono _ _ fun x hx =>
        (SM b' hb' b hb (hanti hb hb' hbb) x hx).1 fun t ht => hn.pow_nonneg t
  · rintro ⟨hmo, hnp⟩
    refine ⟨fun hev => ?_, fun hod => ?_⟩
    · have hn : Odd n := by obtain ⟨k, hk⟩ := hev; exact ⟨k - 1, by omega⟩
      refine caseB fun b hb b' hb' hbb => hDmono _ _ fun x hx =>
        (SM b hb b' hb' (hmo hb hb' hbb) x hx).2 fun t ht =>
          hn.pow_nonpos (ht.2.trans (hnp b' hb'))
    · have hn : Even n := by obtain ⟨k, hk⟩ := hod; exact ⟨k, by omega⟩
      refine caseA fun b hb b' hb' hbb => hDmono _ _ fun x hx =>
        (SM b hb b' hb' (hmo hb hb' hbb) x hx).1 fun t ht => hn.pow_nonneg t
