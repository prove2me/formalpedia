-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.norm_translateL2_sub_h1ToL2_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:11:00.609204+00:00
-- url     : https://prove2.me/submissions/4ac4657d-ef2b-49c6-9530-3e4131294733

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceTranslationEstimateH1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceTranslationEstimateH1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceTranslationEstimateH1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableAddTranslationEstimateH1
variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

-- A.e. formula for translation on L².

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private lemma translateL2_ae_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (g : E →₂[μ] F) :
    (translateL2 (μ := μ) (F := F) a g : E → F) =ᵐ[μ] fun x => (g : E → F) (x + a) := by
  classical
  -- Reduce to `Lp.coeFn_compMeasurePreserving`.
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := (g : MeasureTheory.Lp F (2 : ENNReal) μ))
      (hf := MeasureTheory.measurePreserving_add_right μ a))


-- Fundamental-theorem-of-calculus estimate along a line segment.

private lemma hasDerivAt_line (x a : E) (t : ℝ) :
    HasDerivAt (line (x := x) (a := a)) a t := by
  -- `t ↦ t • a` has derivative `a`, and adding the constant `x` preserves the derivative.
  have hsmul : HasDerivAt (fun t : ℝ => t • a) a t := by
    simpa [one_smul] using (hasDerivAt_id t).smul_const a
  exact HasDerivAt.const_add x hsmul

private lemma deriv_line (x a : E) (t : ℝ) :
    deriv (line (x := x) (a := a)) t = a :=
  (hasDerivAt_line (x := x) (a := a) t).deriv

private lemma hasDerivAt_comp_line
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    HasDerivAt (fun t => f (line (x := x) (a := a) t))
      (fderiv ℝ f (line (x := x) (a := a) t) a) t := by
  have hf' : HasFDerivAt f (fderiv ℝ f (line (x := x) (a := a) t)) (line (x := x) (a := a) t) :=
    (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  exact
    HasFDerivAt.comp_hasDerivAt_of_eq t hf' (hasDerivAt_line (x := x) (a := a) t) rfl

private lemma deriv_comp_line {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    deriv (fun t => f (line (x := x) (a := a) t)) t =
      fderiv ℝ f (line (x := x) (a := a) t) a :=
  (hasDerivAt_comp_line (hf := hf) (x := x) (a := a) t).deriv

/-! ## Pointwise translation bound via the gradient -/

private lemma enorm_fderiv_apply_le_enorm_grad_mul (f : E → ℝ) (x a : E) :
    ‖fderiv ℝ f x a‖ₑ ≤ ‖grad (E := E) f x‖ₑ * ‖a‖ₑ := by
  -- Use the operator norm bound, then identify `‖fderiv‖` with `‖grad‖` via the Riesz isometry.
  have h₁ :
      ‖fderiv ℝ f x a‖ₑ ≤ ‖fderiv ℝ f x‖ₑ * ‖a‖ₑ :=
    (ContinuousLinearMap.le_opENorm (f := fderiv ℝ f x) a)
  have h₂ : ‖grad (E := E) f x‖ₑ = ‖fderiv ℝ f x‖ₑ := by
    -- `grad f x = (toDual).symm (fderiv f x)` and `toDual.symm` is an isometry.
    simp only [grad]
    exact
      (LinearIsometry.enorm_map
        (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
        (fderiv ℝ f x))
  -- Replace the operator norm by the gradient norm.
  simpa [h₂, mul_assoc, mul_left_comm, mul_comm] using h₁

private lemma enorm_deriv_comp_line_le (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ‖deriv (fun t => f (line (x := x) (a := a) t)) t‖ₑ ≤
      ‖a‖ₑ * ‖grad (E := E) f (line (x := x) (a := a) t)‖ₑ := by
  -- Reduce to the `fderiv` bound.
  have :=
    enorm_fderiv_apply_le_enorm_grad_mul
      (E := E) (f := f) (x := line (x := x) (a := a) t) (a := a)
  -- Rewrite `deriv` and commute the product.
  simpa [deriv_comp_line (hf := hf) (x := x) (a := a) t,
    mul_comm, mul_left_comm, mul_assoc] using this

private lemma enorm_sub_le_enorm_mul_lintegral_grad (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ‖f (x + a) - f x‖ₑ ≤
      ‖a‖ₑ * ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖grad (E := E) f (x + t • a)‖ₑ := by
  -- Apply FTC along the segment `t ↦ x + t • a`, then bound the derivative pointwise.
  have hCont :
      ContDiffOn ℝ 1 (fun t : ℝ => f (x + t • a)) (Set.Icc (0 : ℝ) 1) := by
    -- `t ↦ x + t • a` is `C^∞`; compose with `f`.
    have hInner : ContDiff ℝ ⊤ (fun t : ℝ => x + t • a) := by
      simpa [line] using
        (contDiff_const.add (contDiff_id.smul (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => a))))
    have hInner' : ContDiff ℝ 1 (fun t : ℝ => x + t • a) := hInner.of_le (by simp)
    exact (hf.comp hInner').contDiffOn
  have hFTC :
      ‖f (x + a) - f x‖ₑ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ := by
    simpa using
      (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (f := fun t : ℝ => f (x + t • a))
        (a := (0 : ℝ)) (b := 1) hCont (by exact zero_le_one))
  refine hFTC.trans ?_
  have hDerivBound :
      (fun t : ℝ => ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ)
        ≤ᵐ[Measure.restrict volume (Set.Icc (0 : ℝ) 1)]
          fun t : ℝ => ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    -- Pointwise bound holds everywhere.
    refine (ae_of_all _ fun t => ?_)
    -- `deriv` along `t ↦ x + t•a` is controlled by the gradient.
    simpa [line, mul_assoc, mul_left_comm, mul_comm] using
      (enorm_deriv_comp_line_le (x := x) (a := a) (f := f) hf (t := t))
  -- Pull out the constant `‖a‖ₑ`.
  have :
      (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ) ≤
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    exact lintegral_mono_ae hDerivBound
  refine this.trans ?_
  -- Pull out the constant factor.
  have hMeas :
      Measurable fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ := by
    -- `grad f` is continuous when `f` is `C¹`.
    have hgradCont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) (by
      -- `ContDiff` gives continuity of `grad`.
      exact hf)
    -- hence `t ↦ grad f (x + t•a)` is measurable; take `enorm`.
    exact (hgradCont.comp (by
      have : Continuous (fun t : ℝ => x + t • a) := by
        fun_prop
      exact this)).measurable.enorm
  -- Now finish: `∫⁻ t in Set.Icc, ‖a‖ * g t = ‖a‖ * ∫⁻ t in Set.Icc, g t`.
  exact le_of_eq <| by
    simpa [mul_assoc] using
      (MeasureTheory.lintegral_const_mul (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (r := ‖a‖ₑ)
        (f := fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ) hMeas)


-- L² estimate for compactly supported C¹ functions.

private lemma μI_univ : (μI : Measure ℝ) Set.univ = (1 : ℝ≥0∞) := by
  simp [μI, Measure.restrict_apply, Real.volume_Icc]

private lemma holderConj_two_two : (2 : ℝ).HolderConjugate (2 : ℝ) := by
  refine (Real.holderConjugate_iff).2 ?_
  constructor
  · linarith
  · norm_num

private lemma lintegral_rpow_two_le_lintegral_rpow_two
    {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g (μI : Measure ℝ)) :
    (∫⁻ t, g t ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤ ∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
  -- Hölder with `g * 1` gives `∫ g ≤ (∫ g^2)^(1/2) * (∫ 1^2)^(1/2)`.
  have hHolder :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [Pi.mul_apply] using
      (ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := (μI : Measure ℝ)) holderConj_two_two
        hg (aemeasurable_const : AEMeasurable (fun _t : ℝ => (1 : ℝ≥0∞)) (μI : Measure ℝ)))
  have h1 : (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) = (1 : ℝ≥0∞) := by
    -- `μI` has total mass `1`, and `1^2 = 1`.
    simp
  have h :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [h1, mul_one] using hHolder
  -- Raise to the power `2` and simplify `((A)^(1/2))^2 = A`.
  have h' :=
    ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  -- Rewrite the RHS using `rpow_mul`.
  simpa [ENNReal.rpow_mul] using (h'.trans_eq (by
    have : (1 / (2 : ℝ)) * (2 : ℝ) = (1 : ℝ) := by norm_num
    simpa [this] using
      (ENNReal.rpow_mul
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ))
        (1 / (2 : ℝ)) (2 : ℝ)).symm))

omit [IsFiniteMeasureOnCompacts μ] in
/-- `L²` translation estimate for `C¹_c` functions under a right-invariant measure. -/
private lemma lintegral_enorm_sub_sq_le (a : E) (f : ↥(C1c (E := E))) :
    (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
      ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
  -- Pointwise: Cauchy–Schwarz in `t`, then Tonelli in `(x,t)`.
  have hpt :
      ∀ x : E,
        ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
          ‖a‖ₑ ^ (2 : ℝ) *
            ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
    intro x
    have h0 := enorm_sub_le_enorm_mul_lintegral_grad (E := E) (x := x) (a := a) (f := f.1)
      (hf := f.2.1)
    -- Square both sides and apply Cauchy–Schwarz in `t`.
    have h1 :
        ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
          (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
      exact ENNReal.rpow_le_rpow h0 (by norm_num)
    have hcs :
        (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤
          ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
      refine lintegral_rpow_two_le_lintegral_rpow_two (g := fun t : ℝ =>
        ‖grad (E := E) f.1 (x + t • a)‖ₑ) ?_
      -- measurability from continuity of `grad`.
      have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
      have hline : Continuous fun t : ℝ => x + t • a := by
        fun_prop
      exact (hgrad.comp hline).measurable.enorm.aemeasurable
    -- Combine and rewrite.
    calc
      ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ)
          ≤ (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := h1
      _ = ‖a‖ₑ ^ (2 : ℝ) *
          (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
            ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
          simpa using
            (ENNReal.mul_rpow_of_nonneg ‖a‖ₑ
              (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                ∂(μI : Measure ℝ))
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num))
      _ ≤ ‖a‖ₑ ^ (2 : ℝ) *
          ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
            ∂(μI : Measure ℝ) := by
          gcongr
      _ = ‖a‖ₑ ^ (2 : ℝ) *
          ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
            ∂(μI : Measure ℝ) := rfl
  -- Integrate over `x` and apply Tonelli to swap integrals.
  let F : E × ℝ → ℝ≥0∞ :=
    fun z => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ ^ (2 : ℝ)
  have hmeas :
      AEMeasurable
        F (μ.prod (μI : Measure ℝ)) := by
    have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
    have hcont : Continuous fun z : E × ℝ => z.1 + z.2 • a := by
      fun_prop
    have hbase : Measurable fun z : E × ℝ => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ := by
      exact (hgrad.comp hcont).measurable.enorm
    have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
    exact (hpow.comp hbase).aemeasurable
  have hTonelli :
      (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) =
        ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
    -- Tonelli in both orders, via the product measure.
    have hprod :
        (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
          ∫⁻ x, ∫⁻ t, F (x, t) ∂(μI : Measure ℝ) ∂μ :=
      MeasureTheory.lintegral_prod (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
    have hprod_symm :
        (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
          ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) :=
      MeasureTheory.lintegral_prod_symm (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
    calc
      (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ)
          = ∫⁻ z, F z ∂μ.prod (μI : Measure ℝ) := by
              simpa [F] using hprod.symm
      _ = ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) := hprod_symm
      _ = ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
              simp [F]
  -- Now use measure-preserving translation in `x` and evaluate the `t`-integral.
  have hShift :
      (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) =
        ∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ) := by
    refine MeasureTheory.lintegral_congr fun t => ?_
    -- Change of variables `x ↦ x + t•a`.
    have hmeas' : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) := by
      have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
      have hbase : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ := hgrad.measurable.enorm
      have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
        (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
      exact hpow.comp hbase
    simpa [Function.comp, add_assoc] using
      (MeasureTheory.measurePreserving_add_right μ (t • a)).lintegral_comp (μ := μ) (ν := μ)
        (f := fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ)) hmeas'
  have hEval :
      (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) =
        (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
    -- `μI` has total mass `1`.
    simp [μI, Measure.restrict_apply, Real.volume_Icc]
  -- Put everything together.
  have hInt :
      (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
        ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
    calc
      (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ)
          ≤ ∫⁻ x, ‖a‖ₑ ^ (2 : ℝ) *
                ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ := by
            refine MeasureTheory.lintegral_mono ?_
            intro x
            exact hpt x
      _ = ‖a‖ₑ ^ (2 : ℝ) *
            (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) := by
            -- Pull out the constant using `lintegral_const_mul''`.
            have hInner :
                AEMeasurable
                  (fun x : E =>
                    ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) μ := by
              -- Measurability of the inner integral follows
              -- from `hmeas` via
              -- `AEMeasurable.lintegral_prod_right'`.
              simpa [F] using (hmeas.lintegral_prod_right' (μ := μ) (ν := (μI : Measure ℝ)))
            simpa [mul_assoc] using
              (MeasureTheory.lintegral_const_mul'' (μ := μ) (r := ‖a‖ₑ ^ (2 : ℝ))
                (f := fun x : E =>
                  ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) hInner)
      _ = ‖a‖ₑ ^ (2 : ℝ) *
            (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) := by
            exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hTonelli
      _ = ‖a‖ₑ ^ (2 : ℝ) *
            (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) := by
            exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hShift
      _ = ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
            exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hEval
  exact hInt

private lemma enorm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ₑ ≤
      ‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ := by
  classical
  -- Reduce to an `eLpNorm` inequality on representatives.
  have hL2 :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
          toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => (f.1 (x + a) - f.1 x)) (2 : ℝ≥0∞) μ := by
    -- Both terms agree a.e. with the underlying pointwise translation.
    have h₁ :
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) := by
      have hf :
          (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
        (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
      have hf' :
          (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
        exact
          (Measure.QuasiMeasurePreserving.ae_eq_comp
            (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
      exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
    have h₂ : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] fun x => f.1 x :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hsub :
        ((translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
              toL2 (μ := μ) (E := E) f : E →₂[μ] ℝ) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) - f.1 x := by
      filter_upwards [Lp.coeFn_sub
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f))
        (toL2 (μ := μ) (E := E) f), h₁, h₂] with x hxsub hx1 hx2
      simpa [hx1, hx2, Pi.sub_apply] using hxsub
    -- Convert the `Lp` norm to `eLpNorm` and rewrite using a.e. equality.
    let d : E →₂[μ] ℝ :=
      translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) - toL2 (μ := μ) (E := E) f
    have hd0 : (‖d‖ₑ : ℝ≥0∞) = MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have hd1 :
        MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) (by simpa [d] using hsub)
    simpa [d] using hd0.trans hd1
  have hGrad :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    have h₁ :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] fun x => grad (E := E) f.1 x :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have h0 :
        (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
          MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have h1 :
        MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) h₁
    exact h0.trans h1
  -- Prove the `eLpNorm` inequality by squaring, using Tonelli and measure-preserving translation.
  have hCore :
      MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ ≤
        ‖a‖ₑ * MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    -- Expand the definition of `eLpNorm` at exponent `2`.
    have h2_ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
    have h2_netop : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by simp
    have hf_meas : MeasureTheory.AEStronglyMeasurable (fun x : E => f.1 x) μ :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).aestronglyMeasurable
    have hshift_meas :
        MeasureTheory.AEStronglyMeasurable (fun x : E => f.1 (x + a) - f.1 x) μ := by
      have hshift : MeasureTheory.AEStronglyMeasurable (fun x : E => f.1 (x + a)) μ :=
        hf_meas.comp_quasiMeasurePreserving
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving
      exact hshift.sub hf_meas
    have hgrad_meas :
        MeasureTheory.AEStronglyMeasurable (fun x : E => grad (E := E) f.1 x) μ :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).aestronglyMeasurable
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne0 h2_netop,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne0 h2_netop,
      ENNReal.toReal_ofNat]
    -- It suffices to compare the squared integrals.
    have hsq := lintegral_enorm_sub_sq_le (μ := μ) a f
    -- Take the `1/2` power on both sides and simplify.
    have hsq' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ) * ∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      exact ENNReal.rpow_le_rpow hsq (by norm_num)
    -- Rewrite the RHS as `‖a‖ * (...)^(1/2)`.
    have hsq'' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      simpa [ENNReal.mul_rpow_of_nonneg, show (0 : ℝ) ≤ (1 / (2 : ℝ)) by nlinarith,
        mul_assoc, mul_left_comm, mul_comm] using hsq'
    have hroot : (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = ‖a‖ₑ := by
      -- `(x^2)^(1/2) = x` in `ℝ≥0∞`, accounting for simp-normalization of `2` and `1/2`.
      have hnat : (‖a‖ₑ ^ (2 : ℕ)) = ‖a‖ₑ ^ (2 : ℝ) := by
        simp
      calc
        (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = (‖a‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
          congrArg (fun r : ℝ≥0∞ => r ^ ((2 : ℝ)⁻¹)) hnat
        _ = ‖a‖ₑ := by
          have := (ENNReal.rpow_mul ‖a‖ₑ (2 : ℝ) ((2 : ℝ)⁻¹)).symm
          have hmul : (2 : ℝ) * ((2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
          simpa [hmul, ENNReal.rpow_one] using this
    simpa [hroot, mul_assoc, mul_left_comm, mul_comm] using hsq''
  -- Finish: translate back to the original `L²` norms.
  -- (The final `simp` is safe since we have explicit `eLpNorm` equalities above.)
  simpa [hL2, hGrad] using hCore

/-- Real-norm form of `enorm_translateL2_sub_toL2_le`. -/
private lemma norm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ ≤
      ‖a‖ * ‖toL2Grad (μ := μ) (E := E) f‖ := by
  have h := enorm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hA_ne_top :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    simp [enorm]
  have hGrad_ne_top :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    simp [enorm]
  have hB_ne_top : (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    refine ENNReal.mul_ne_top ?_ hGrad_ne_top
    simp [enorm]
  have h' :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ).toReal ≤
        (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ).toReal := by
    exact (ENNReal.toReal_le_toReal hA_ne_top hB_ne_top).2 h
  simpa only [ENNReal.toReal_mul, toReal_enorm] using h'


-- Extension from the graph of C¹_c functions to its closure H¹.
theorem solution (a : E) (u : ↥(h1 (μ := μ) (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (h1ToL2 (μ := μ) (E := E) u) -
        h1ToL2 (μ := μ) (E := E) u‖ ≤
      ‖a‖ * ‖h1ToL2Grad (μ := μ) (E := E) u‖ := by
  classical
  -- Work in the ambient space `L² × L²(E)`.
  let V : Type _ := (E →₂[μ] ℝ) × (E →₂[μ] E)
  let S : Set V :=
    {v |
      ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ ≤
        ‖a‖ * ‖v.2‖}
  have hS_closed : IsClosed S := by
    -- Closedness follows from continuity of both sides.
    have hf :
        Continuous fun v : V =>
          ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ := by
      -- `v ↦ v.1` is continuous, translation is continuous,
      -- subtraction is continuous, and norm is continuous.
      have hfst : Continuous fun v : V => v.1 := continuous_fst
      have htr :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 := by
        -- `translateL2` is a continuous linear isometry.
        exact (translateL2 (μ := μ) (F := ℝ) a).toContinuousLinearMap.continuous.comp hfst
      have hsub :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 - v.1 := by
        exact htr.sub hfst
      exact (continuous_norm.comp hsub)
    have hg :
        Continuous fun v : V =>
          ‖a‖ * ‖v.2‖ := by
      have hsnd : Continuous fun v : V => v.2 := continuous_snd
      have hnorm : Continuous fun v : V => ‖v.2‖ := continuous_norm.comp hsnd
      exact (continuous_const.mul hnorm)
    exact isClosed_le hf hg
  have hRange : (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S := by
    rintro v ⟨f, rfl⟩
    -- Reduce to the `C¹_c` estimate.
    simpa [S, graph, toL2Linear, toL2GradLinear] using
      norm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hClosure :
      closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S :=
    closure_minimal hRange hS_closed
  have hu :
      (u : V) ∈ closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) := by
    -- `u ∈ H¹` means `u` is in the topological closure of the range of `graph`.
    have hu0 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := by
      have hu0 : (u : V) ∈ h1 (μ := μ) (E := E) := u.2
      dsimp [h1] at hu0
      exact hu0
    have hu1 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := hu0
    rw [Submodule.topologicalClosure_coe] at hu1
    exact hu1
  have huS : (u : V) ∈ S := hClosure hu
  -- Unpack membership in `S` and rewrite in terms of the bundled maps `h1ToL2` and `h1ToL2Grad`.
  simpa [S, V, h1ToL2, h1ToL2Grad] using huS
