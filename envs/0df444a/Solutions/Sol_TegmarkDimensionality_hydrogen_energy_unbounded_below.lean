-- Prove2me | solution 1 for TegmarkDimensionality.hydrogen_energy_unbounded_below
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:55:25.289138+00:00
-- url     : https://prove2.me/submissions/5d0eb0f5-50a9-43ab-a4ed-30226b129fe6

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
set_option autoImplicit false

open MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem dilation_fderiv (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f) (c l : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => c * f (l • y)) x = (c * l) • fderiv ℝ f (l • x) := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    l • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
  have hd := ((hf (L x)).hasFDerivAt.comp x L.hasFDerivAt).const_smul c
  have hd' : HasFDerivAt (fun y => c * f (l • y))
      ((c * l) • fderiv ℝ f (l • x)) x := by
    convert! hd using 1
    ext y
    simp [L, smul_smul, mul_assoc]
  exact hd'.fderiv

theorem dilation_mass (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c l : ℝ) (hl : 0 < l) :
    (∫ x, (c * f (l • x)) ^ 2) = c ^ 2 * (l ^ n)⁻¹ * (∫ x, f x ^ 2) := by
  simp_rw [mul_pow]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (fun x : EuclideanSpace ℝ (Fin n) => f x ^ 2) l (hR := hl.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, mul_assoc]

theorem dilation_kinetic (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f) (c l : ℝ) (hl : 0 < l) :
    (∫ x, ‖fderiv ℝ (fun y => c * f (l • y)) x‖ ^ 2) =
      c ^ 2 * l ^ 2 * (l ^ n)⁻¹ * (∫ x, ‖fderiv ℝ f x‖ ^ 2) := by
  simp_rw [dilation_fderiv n f hf, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (fun x : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ f x‖ ^ 2) l (hR := hl.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, mul_assoc, mul_pow]

theorem dilation_weighted_mass (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c l p : ℝ) (hl : 0 < l) :
    (∫ x, ‖x‖ ^ p * (c * f (l • x)) ^ 2) =
      c ^ 2 * l ^ (-p) * (l ^ n)⁻¹ * (∫ x, ‖x‖ ^ p * f x ^ 2) := by
  have hr (x : EuclideanSpace ℝ (Fin n)) : ‖l • x‖ ^ p = l ^ p * ‖x‖ ^ p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl, Real.mul_rpow hl.le (norm_nonneg x)]
  have he : l ^ (-p) * l ^ p = 1 := by
    rw [← Real.rpow_add hl]
    simp
  have hp (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ^ p * (c * f (l • x)) ^ 2 =
      (c ^ 2 * l ^ (-p)) * (‖l • x‖ ^ p * f (l • x) ^ 2) := by
    rw [hr]
    linear_combination -(c ^ 2 * ‖x‖ ^ p * f (l • x) ^ 2) * he
  simp_rw [hp]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ p * f x ^ 2) l (hR := hl.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, mul_assoc]

theorem normalized_dilation_exists (n : ℕ) (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hM : 0 < ∫ x, f x ^ 2) (κ l : ℝ) (hl : 0 < l) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∫ x, ψ x ^ 2) = 1 ∧
        (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) - κ * (∫ x, ‖x‖ ^ ((2 : ℝ) - n) * ψ x ^ 2) =
          (l ^ 2 * (∫ x, ‖fderiv ℝ f x‖ ^ 2) -
            κ * l ^ (n - 2) * (∫ x, ‖x‖ ^ ((2 : ℝ) - n) * f x ^ 2)) / (∫ x, f x ^ 2) := by
  let M : ℝ := ∫ x, f x ^ 2
  let c : ℝ := Real.sqrt (l ^ n / M)
  have hM0 : M ≠ 0 := hM.ne'
  have hln : l ^ n ≠ 0 := pow_ne_zero n hl.ne'
  have hc2 : c ^ 2 = l ^ n / M := Real.sq_sqrt (by positivity)
  let ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => c * f (l • x)
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    l • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
  have hψ : ContDiff ℝ ∞ ψ := by
    simpa only [ψ, L, smul_apply, ContinuousLinearMap.id_apply,
      Function.comp_def, smul_eq_mul] using! (hf.comp L.contDiff).const_smul c
  have hs' : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin n) => f (l • x)) := by
    simpa [Function.comp_def, Units.smul_def] using!
      hs.comp_homeomorph (Homeomorph.smul (Units.mk0 l hl.ne'))
  have hψs : HasCompactSupport ψ := by
    simpa only [ψ, Pi.mul_apply] using! hs'.mul_left (f := fun _ => c)
  refine ⟨ψ, hψ, hψs, ?_, ?_⟩
  · rw [dilation_mass n f c l hl, hc2]
    change (l ^ n / M) * (l ^ n)⁻¹ * M = 1
    field_simp
  · rw [dilation_kinetic n f (hf.differentiable (by norm_num)) c l hl,
      dilation_weighted_mass n f c l ((2 : ℝ) - n) hl]
    have hp : l ^ (-((2 : ℝ) - n)) = l ^ (n - 2) := by
      rw [show -((2 : ℝ) - n) = ((n - 2 : ℕ) : ℝ) by
        rw [Nat.cast_sub hn]; norm_num, Real.rpow_natCast]
    rw [hp, hc2]
    dsimp [M]
    field_simp


/-- In dimension at least five, the attractive term of a dilated seed
dominates its kinetic term at every positive coupling. -/
theorem polynomial_energy_unbounded (n : ℕ) (hn : 4 < n) (κ : ℝ) (hκ : 0 < κ)
    (K P E : ℝ) (hP : 0 < P) :
    ∃ l : ℝ, 0 < l ∧ l ^ 2 * K - κ * l ^ (n - 2) * P < E := by
  obtain ⟨l, hl⟩ := exists_gt (max 1 (max ((K + 1) / (κ * P)) (-E)))
  have hl1 : 1 < l := lt_of_le_of_lt (le_max_left _ _) hl
  have hl0 : 0 < l := lt_trans zero_lt_one hl1
  have hlt : (K + 1) / (κ * P) < l :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hl
  have hlE : -E < l :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hl
  have hκP : 0 < κ * P := mul_pos hκ hP
  have hcoeff : K - κ * l * P < -1 := by
    have h := (div_lt_iff₀ hκP).mp hlt
    nlinarith
  have hm : 1 ≤ n - 4 := by omega
  have hpow : l ≤ l ^ (n - 4) := by
    simpa using pow_le_pow_right₀ hl1.le hm
  have hpower : l ^ (n - 2) = l ^ 2 * l ^ (n - 4) := by
    rw [show n - 2 = 2 + (n - 4) by omega, pow_add]
  have henergy : l ^ 2 * K - κ * l ^ (n - 2) * P < -(l ^ 2) := by
    rw [hpower]
    have h1 := mul_le_mul_of_nonneg_left hpow (show 0 ≤ κ * P from hκP.le)
    have h2 : K - κ * l ^ (n - 4) * P < -1 := by nlinarith
    have h3 := mul_lt_mul_of_pos_left h2 (sq_pos_of_pos hl0)
    nlinarith
  refine ⟨l, hl0, henergy.trans ?_⟩
  have hs : l ≤ l ^ 2 := by nlinarith
  linarith

/-- Once a four-dimensional seed has negative energy, its scale produces
arbitrarily negative normalized energy. -/
theorem critical_energy_unbounded (A E : ℝ) (hA : A < 0) :
    ∃ l : ℝ, 0 < l ∧ l ^ 2 * A < E := by
  obtain ⟨l, hl⟩ := exists_gt (max 1 (E / A))
  have hl1 : 1 < l := lt_of_le_of_lt (le_max_left _ _) hl
  have hlEA : E / A < l := lt_of_le_of_lt (le_max_right _ _) hl
  have hs : l ≤ l ^ 2 := by nlinarith
  have h : l * A < E := (div_lt_iff_of_neg hA).mp hlEA
  exact ⟨l, lt_trans zero_lt_one hl1, (mul_le_mul_of_nonpos_right hs hA.le).trans_lt h⟩


open MeasureTheory
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem continuous_weighted_square (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (ε : ℝ) (hε : 0 < ε) (hz : ∀ x, ‖x‖ < ε → f x = 0) (p : ℝ) :
    Continuous (fun x => ‖x‖ ^ p * f x ^ 2) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x = 0
  · subst x
    have he : (fun x => ‖x‖ ^ p * f x ^ 2) =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin n))]
        (fun _ => 0) := by
      filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds (by simpa using hε))]
        with y hy
      simp [hz y hy]
    exact continuousAt_const.congr_of_eventuallyEq he
  · exact (continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.mpr hx))).mul
      (hf.continuousAt.pow 2)

theorem positive_compact_seed (n : ℕ) (hn : 0 < n) (p : ℝ) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (0 < ∫ x, f x ^ 2) ∧ (0 < ∫ x, ‖x‖ ^ p * f x ^ 2) := by
  let a : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 2
  have ha : ‖a‖ = 2 := by simp [a]
  let b : ContDiffBump a := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hb : b a = 1 := b.one_of_mem_closedBall (by simp [b])
  have hz (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < 1) : b x = 0 := by
    apply b.zero_of_le_dist
    have h := norm_sub_norm_le a x
    rw [ha] at h
    rw [dist_eq_norm]
    dsimp [b]
    rw [norm_sub_rev] at h
    linarith
  have hsq : HasCompactSupport (fun x => b x ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using! b.hasCompactSupport.mul_left (f := b)
  have hc : Continuous (fun x => b x ^ 2) := b.continuous.pow 2
  have hp : Continuous (fun x => ‖x‖ ^ p * b x ^ 2) :=
    continuous_weighted_square n b b.continuous 1 zero_lt_one hz p
  have hps : HasCompactSupport (fun x => ‖x‖ ^ p * b x ^ 2) :=
    hsq.mul_left
  refine ⟨b, b.contDiff, b.hasCompactSupport,
    hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := a) hsq (fun x => sq_nonneg _) ?_,
    hp.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := a) hps
      (fun x => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)) ?_⟩
  · simp [hb]
  · rw [ha, hb]
    positivity


theorem hydrogen_energy_unbounded_dim_ge_five (n : ℕ) (hn : 4 < n)
    (κ : ℝ) (hκ : 0 < κ) (E : ℝ) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∫ x, ψ x ^ 2) = 1 ∧
        (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) -
          κ * (∫ x, ‖x‖ ^ ((2 : ℝ) - n) * ψ x ^ 2) < E := by
  obtain ⟨f, hf, hs, hM, hP⟩ := positive_compact_seed n (by omega) ((2 : ℝ) - n)
  obtain ⟨l, hl, henergy⟩ := polynomial_energy_unbounded n hn κ hκ
    (∫ x, ‖fderiv ℝ f x‖ ^ 2) (∫ x, ‖x‖ ^ ((2 : ℝ) - n) * f x ^ 2)
    (E * (∫ x, f x ^ 2)) hP
  obtain ⟨ψ, hψ, hψs, hψM, hψE⟩ :=
    normalized_dilation_exists n (by omega) f hf hs hM κ l hl
  refine ⟨ψ, hψ, hψs, hψM, ?_⟩
  rw [hψE]
  exact (div_lt_iff₀ hM).mpr henergy

theorem hydrogen_energy_unbounded_dim_four_of_negative_seed
    (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (hM : 0 < ∫ x, f x ^ 2) (κ E : ℝ)
    (hneg : (∫ x, ‖fderiv ℝ f x‖ ^ 2) -
      κ * (∫ x, ‖x‖ ^ ((2 : ℝ) - 4) * f x ^ 2) < 0) :
    ∃ ψ : EuclideanSpace ℝ (Fin 4) → ℝ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∫ x, ψ x ^ 2) = 1 ∧
        (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) -
          κ * (∫ x, ‖x‖ ^ ((2 : ℝ) - 4) * ψ x ^ 2) < E := by
  obtain ⟨l, hl, henergy⟩ := critical_energy_unbounded _ (E * (∫ x, f x ^ 2)) hneg
  obtain ⟨ψ, hψ, hψs, hψM, hψE⟩ :=
    normalized_dilation_exists 4 (by norm_num) f hf hs hM κ l hl
  simp only [Nat.cast_ofNat, Nat.reduceSub] at hψE
  refine ⟨ψ, hψ, hψs, hψM, ?_⟩
  rw [hψE]
  apply (div_lt_iff₀ hM).mpr
  convert! henergy using 1
  ring


open MeasureTheory Set
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem hasFDerivAt_norm_inner (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    HasFDerivAt norm (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have he : (fun y : EuclideanSpace ℝ (Fin n) => Real.sqrt (‖y‖ ^ 2)) = norm :=
    funext fun y => Real.sqrt_sq (norm_nonneg y)
  rw [he, Real.sqrt_sq (norm_nonneg x)] at h
  convert! h using 1
  ext y
  simp only [smul_apply, smul_eq_mul]
  field_simp
  simp [mul_comm]

theorem radial_fderiv_norm_sq (n : ℕ) (F : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ≠ 0) (hF : DifferentiableAt ℝ F ‖x‖) :
    ‖fderiv ℝ (fun y => F ‖y‖) x‖ ^ 2 = (deriv F ‖x‖) ^ 2 := by
  have hd := hF.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_norm_inner n x hx)
  have he : fderiv ℝ (fun y => F ‖y‖) x =
      (deriv F ‖x‖ * ‖x‖⁻¹) • innerSL ℝ x := by
    simpa only [Function.comp_def, smul_smul] using! hd.fderiv
  rw [he, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, mul_pow, sq_abs]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

theorem integral_log_radial (g : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), r⁻¹ * g (Real.log r)) = ∫ t, g t := by
  have he : Real.exp '' (univ : Set ℝ) = Ioi 0 := by
    ext r
    constructor
    · rintro ⟨t, _, rfl⟩; exact Real.exp_pos t
    · intro hr; exact ⟨Real.log r, mem_univ _, Real.exp_log hr⟩
  rw [← he, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun _ _ _ _ h => Real.exp_injective h)]
  simp [Real.exp_pos, abs_of_pos, smul_eq_mul, Real.exp_ne_zero]


open MeasureTheory Set
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem annulus_profile_deriv (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (L r : ℝ) (hL : 0 < L) (hr : 0 < r) :
    HasDerivAt (fun t => χ (Real.log t / L) / t)
      ((deriv χ (Real.log r / L) / L - χ (Real.log r / L)) / r ^ 2) r := by
  have hd := ((hχ.differentiable (by norm_num) (Real.log r / L)).hasDerivAt.comp r
    ((Real.hasDerivAt_log hr.ne').div_const L)).div (hasDerivAt_id r) hr.ne'
  convert! hd using 1
  dsimp [Function.comp_def, id]
  field_simp

theorem annulus_function_smooth_compact (n : ℕ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hz : ∀ t, t ≤ 1 ∨ 3 ≤ t → χ t = 0)
    (L : ℝ) (hL : 0 < L) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => χ (Real.log ‖x‖ / L) / ‖x‖) ∧
      HasCompactSupport (fun x : EuclideanSpace ℝ (Fin n) => χ (Real.log ‖x‖ / L) / ‖x‖) := by
  have hzero (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < 1) :
      χ (Real.log ‖x‖ / L) / ‖x‖ = 0 := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hl : Real.log ‖x‖ ≤ 0 := Real.log_nonpos (norm_nonneg x) hx.le
      rw [hz _ (Or.inl (by
        have : Real.log ‖x‖ / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg hl hL.le
        linarith)), zero_div]
  constructor
  · refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : x = 0
    · subst x
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [continuous_norm.continuousAt.eventually
        (gt_mem_nhds (by norm_num : ‖(0 : EuclideanSpace ℝ (Fin n))‖ < 1))] with y hy
      exact hzero y hy
    · have hn : ContDiffAt ℝ ∞ (norm : EuclideanSpace ℝ (Fin n) → ℝ) x :=
        contDiffAt_norm ℝ hx
      exact ((hχ.contDiffAt.comp x ((hn.log (norm_ne_zero_iff.mpr hx)).div_const L))).div
        hn (norm_ne_zero_iff.mpr hx)
  · apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.exp (3 * L)))
    intro x hx
    by_contra hnot
    have hxr : Real.exp (3 * L) < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hnot
    have hxp : 0 < ‖x‖ := (Real.exp_pos _).trans hxr
    have ht : 3 ≤ Real.log ‖x‖ / L := by
      rw [le_div_iff₀ hL, Real.le_log_iff_exp_le hxp]
      exact hxr.le
    exact hx (by simp [hz _ (Or.inr ht)])

theorem compact_cutoff_exists :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ χ 2 = 1 ∧
      ∀ t, t ≤ 1 ∨ 3 ≤ t → χ t = 0 := by
  let b : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, b.one_of_mem_closedBall (by simp [b]), ?_⟩
  intro t ht
  apply b.zero_of_le_dist
  rcases ht with h | h
  · rw [Real.dist_eq, abs_of_nonpos (by linarith : t - 2 ≤ 0)]
    dsimp [b]
    linarith
  · rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ t - 2)]
    dsimp [b]
    linarith


open MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem cutoff_cross_integral_zero (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) : (∫ t, χ t * deriv χ t) = 0 := by
  have hc : Continuous (deriv χ) := hχ.continuous_deriv (by norm_num)
  have hi : Integrable (χ * deriv χ) :=
    (hχ.continuous.mul hc).integrable_of_hasCompactSupport hs.mul_right
  have hi' : Integrable (deriv χ * χ) :=
    (hc.mul hχ.continuous).integrable_of_hasCompactSupport hs.mul_left
  have hsq : Integrable (χ * χ) :=
    (hχ.continuous.mul hχ.continuous).integrable_of_hasCompactSupport hs.mul_right
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := χ) (v := χ) (u' := deriv χ) (v' := deriv χ)
    (fun x _ => (hχ.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hχ.differentiable (by norm_num) x).hasDerivAt) hi hi' hsq
  simp_rw [mul_comm (deriv χ _) (χ _)] at he
  linarith

theorem cutoff_energy_integral (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (L : ℝ) (_hL : 0 < L) :
    (∫ t, (deriv χ t / L - χ t) ^ 2) =
      (∫ t, deriv χ t ^ 2) / L ^ 2 + ∫ t, χ t ^ 2 := by
  have hc : Continuous (deriv χ) := hχ.continuous_deriv (by norm_num)
  have hsχ : HasCompactSupport (fun t => χ t ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using! hs.mul_right (f' := χ)
  have hsd : HasCompactSupport (fun t => deriv χ t ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using! hs.deriv.mul_right (f' := deriv χ)
  have hsi : Integrable (fun t => χ t ^ 2) :=
    (hχ.continuous.pow 2).integrable_of_hasCompactSupport hsχ
  have hdi : Integrable (fun t => deriv χ t ^ 2) :=
    (hc.pow 2).integrable_of_hasCompactSupport hsd
  have hci : Integrable (fun t => χ t * deriv χ t) := by
    simpa only [Pi.mul_apply] using!
      (hχ.continuous.mul hc).integrable_of_hasCompactSupport hs.mul_right
  have he (t : ℝ) : (deriv χ t / L - χ t) ^ 2 =
      L⁻¹ ^ 2 * deriv χ t ^ 2 - (2 / L) * (χ t * deriv χ t) + χ t ^ 2 := by ring
  simp_rw [he]
  have hadd :
      (∫ t, L⁻¹ ^ 2 * deriv χ t ^ 2 - (2 / L) * (χ t * deriv χ t) + χ t ^ 2) =
        (∫ t, L⁻¹ ^ 2 * deriv χ t ^ 2 - (2 / L) * (χ t * deriv χ t)) +
          ∫ t, χ t ^ 2 := by
    simpa only [Pi.sub_apply] using!
      integral_add ((hdi.const_mul (L⁻¹ ^ 2)).sub (hci.const_mul (2 / L))) hsi
  have hsub :
      (∫ t, L⁻¹ ^ 2 * deriv χ t ^ 2 - (2 / L) * (χ t * deriv χ t)) =
        (∫ t, L⁻¹ ^ 2 * deriv χ t ^ 2) - ∫ t, (2 / L) * (χ t * deriv χ t) := by
    simpa only [Pi.sub_apply] using!
      integral_sub (hdi.const_mul (L⁻¹ ^ 2)) (hci.const_mul (2 / L))
  rw [hadd, hsub, integral_const_mul,
    integral_const_mul, cutoff_cross_integral_zero χ hχ hs]
  simp [div_eq_mul_inv, mul_comm]

theorem cutoff_negative_energy_exists (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (hne : χ 2 ≠ 0) (κ : ℝ) (hκ : 1 < κ) :
    ∃ L : ℝ, 0 < L ∧ (∫ t, (deriv χ t / L - χ t) ^ 2) - κ * (∫ t, χ t ^ 2) < 0 := by
  have hsc : HasCompactSupport (fun t => χ t ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using! hs.mul_right (f' := χ)
  have hM : 0 < ∫ t, χ t ^ 2 :=
    (hχ.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := 2) hsc (fun t => sq_nonneg _) (pow_ne_zero 2 hne)
  let K : ℝ := ∫ t, deriv χ t ^ 2
  let M : ℝ := ∫ t, χ t ^ 2
  have hδ : 0 < (κ - 1) * M := mul_pos (sub_pos.mpr hκ) hM
  obtain ⟨L, hL⟩ := exists_gt (max 1 (K / ((κ - 1) * M)))
  have hL1 : 1 < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hLp : 0 < L := zero_lt_one.trans hL1
  have hKL : K < (κ - 1) * M * L := by
    simpa only [mul_comm L] using
      (div_lt_iff₀ hδ).mp (lt_of_le_of_lt (le_max_right _ _) hL)
  have hLL : L < L ^ 2 := by nlinarith
  have hKL2 : K / L ^ 2 < (κ - 1) * M :=
    (div_lt_iff₀ (sq_pos_of_pos hLp)).mpr (hKL.trans (mul_lt_mul_of_pos_left hLL hδ))
  refine ⟨L, hLp, ?_⟩
  rw [cutoff_energy_integral χ hχ hs L hLp]
  change K / L ^ 2 + M - κ * M < 0
  nlinarith


theorem integral_log_div (g : ℝ → ℝ) (L : ℝ) (hL : 0 < L) :
    (∫ r in Ioi (0 : ℝ), r⁻¹ * g (Real.log r / L)) = L * ∫ t, g t := by
  rw [integral_log_radial (fun t => g (t / L)), Measure.integral_comp_div]
  simp only [abs_of_pos hL, smul_eq_mul]

theorem annulus_energy_integrals (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (L : ℝ) (hL : 0 < L) :
    let f : EuclideanSpace ℝ (Fin 4) → ℝ := fun x => χ (Real.log ‖x‖ / L) / ‖x‖
    let V : ℝ := volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (∫ x, ‖fderiv ℝ f x‖ ^ 2) = 4 * V * L * (∫ t, (deriv χ t / L - χ t) ^ 2) ∧
      (∫ x, ‖x‖ ^ ((2 : ℝ) - 4) * f x ^ 2) = 4 * V * L * (∫ t, χ t ^ 2) := by
  dsimp only
  let A : ℝ → ℝ := fun t => deriv χ t / L - χ t
  have hder (x : EuclideanSpace ℝ (Fin 4)) (hx : x ≠ 0) :
      ‖fderiv ℝ (fun y => χ (Real.log ‖y‖ / L) / ‖y‖) x‖ ^ 2 =
        (A (Real.log ‖x‖ / L) / ‖x‖ ^ 2) ^ 2 := by
    have hd := annulus_profile_deriv χ hχ L ‖x‖ hL (norm_pos_iff.mpr hx)
    rw [radial_fderiv_norm_sq 4 (fun r => χ (Real.log r / L) / r) x hx
      hd.differentiableAt, hd.deriv]
  constructor
  · calc
      _ = ∫ x : EuclideanSpace ℝ (Fin 4), (A (Real.log ‖x‖ / L) / ‖x‖ ^ 2) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin 4))] with x hx
        exact hder x hx
      _ = 4 * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1) *
          (∫ r in Ioi (0 : ℝ), r ^ 3 * (A (Real.log r / L) / r ^ 2) ^ 2) := by
        simpa only [finrank_euclideanSpace_fin, Nat.reduceSub, nsmul_eq_mul, Nat.cast_ofNat,
          smul_eq_mul, mul_assoc] using
          integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 4)))
            (fun r => (A (Real.log r / L) / r ^ 2) ^ 2)
      _ = 4 * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1) *
          (∫ r in Ioi (0 : ℝ), r⁻¹ * (A (Real.log r / L)) ^ 2) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        have hr0 : r ≠ 0 := ne_of_gt hr
        field_simp
      _ = _ := by
        rw [integral_log_div (fun t => A t ^ 2) L hL]
        dsimp [A]
        ring
  · calc
      _ = 4 * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1) *
          (∫ r in Ioi (0 : ℝ), r ^ 3 * (r ^ ((2 : ℝ) - 4) * (χ (Real.log r / L) / r) ^ 2)) := by
        simpa only [finrank_euclideanSpace_fin, Nat.reduceSub, nsmul_eq_mul, Nat.cast_ofNat,
          smul_eq_mul, mul_assoc] using
          integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 4)))
            (fun r => r ^ ((2 : ℝ) - 4) * (χ (Real.log r / L) / r) ^ 2)
      _ = 4 * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1) *
          (∫ r in Ioi (0 : ℝ), r⁻¹ * (χ (Real.log r / L)) ^ 2) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        rw [show (2 : ℝ) - 4 = -(2 : ℝ) by norm_num, Real.rpow_neg hr.le, Real.rpow_two]
        have hr0 : r ≠ 0 := ne_of_gt hr
        field_simp
      _ = _ := by
        rw [integral_log_div (fun t => χ t ^ 2) L hL]
        ring


theorem hydrogen_negative_seed_dim_four (κ : ℝ) (hκ : 1 < κ) :
    ∃ f : EuclideanSpace ℝ (Fin 4) → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (0 < ∫ x, f x ^ 2) ∧
      (∫ x, ‖fderiv ℝ f x‖ ^ 2) - κ * (∫ x, ‖x‖ ^ ((2 : ℝ) - 4) * f x ^ 2) < 0 := by
  obtain ⟨χ, hχ, hsχ, hχ2, hz⟩ := compact_cutoff_exists
  obtain ⟨L, hL, hneg⟩ := cutoff_negative_energy_exists χ hχ hsχ (by simp [hχ2]) κ hκ
  let f : EuclideanSpace ℝ (Fin 4) → ℝ := fun x => χ (Real.log ‖x‖ / L) / ‖x‖
  obtain ⟨hf, hs⟩ := annulus_function_smooth_compact 4 χ hχ hz L hL
  let a : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single ⟨0, by norm_num⟩ (Real.exp (2 * L))
  have ha : ‖a‖ = Real.exp (2 * L) := by simp [a, abs_of_pos (Real.exp_pos _)]
  have hfa : f a ≠ 0 := by
    dsimp [f]
    rw [ha, Real.log_exp, mul_div_cancel_right₀ 2 hL.ne', hχ2]
    exact div_ne_zero one_ne_zero (Real.exp_ne_zero _)
  have hfsq : HasCompactSupport (fun x => f x ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using! hs.mul_right (f' := f)
  have hM : 0 < ∫ x, f x ^ 2 :=
    (hf.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := a) hfsq (fun x => sq_nonneg _) (pow_ne_zero 2 hfa)
  obtain ⟨hK, hP⟩ := annulus_energy_integrals χ hχ L hL
  have hV : 0 < volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' (by finiteness)
  refine ⟨f, hf, hs, hM, ?_⟩
  change (∫ x, ‖fderiv ℝ (fun y => χ (Real.log ‖y‖ / L) / ‖y‖) x‖ ^ 2) -
    κ * (∫ x : EuclideanSpace ℝ (Fin 4), ‖x‖ ^ ((2 : ℝ) - 4) *
      (χ (Real.log ‖x‖ / L) / ‖x‖) ^ 2) < 0
  rw [hK, hP]
  have hh := mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hV) hL) hneg
  nlinarith

theorem solution (n : ℕ) (hn : 3 < n) (κ : ℝ) (hκ : 0 < κ)
    (hκ4 : n = 4 → 1 < κ) (E : ℝ) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∫ x, ψ x ^ 2) = 1 ∧
      (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) - κ * (∫ x, ‖x‖ ^ ((2 : ℝ) - n) * ψ x ^ 2) < E := by
  by_cases h4 : n = 4
  · subst n
    obtain ⟨f, hf, hs, hM, hneg⟩ := hydrogen_negative_seed_dim_four κ (hκ4 rfl)
    simpa only [Nat.cast_ofNat] using!
      hydrogen_energy_unbounded_dim_four_of_negative_seed f hf hs hM κ E hneg
  · exact hydrogen_energy_unbounded_dim_ge_five n (by omega) κ hκ E
