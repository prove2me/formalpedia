-- Prove2me | solution 1 for PVM.phaseUnitaryGroup_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:10:47.957065+00:00
-- url     : https://prove2.me/submissions/85a65383-f10c-49ae-acf7-a04238014c07

import Definitions.Def_Spectral_Stone_SelfAdjoint
import Definitions.Def_Spectral_Spectral_Existence
import Definitions.Def_Spectral_Stone_Theorem
import Theorems.Thm_PVM_integral_mul
import Theorems.Thm_PVM_ofReal_norm_sq_integral_sub_unboundedIntegral
import Theorems.Thm_PVM_simpleIntegral_const
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
import Theorems.Thm_PVM_tendsto_simpleIntegral_of_tendstoUniformly
import Theorems.Thm_StrongContUnitary_mem_generator_domain_iff
import Theorems.Thm_StrongContUnitary_tendsto_generator
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


section
open MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem PVM.integral_const_local (E_pvm : PVM E) (z : ℂ) :
    E_pvm.integral (fun _ : ℝ => z) measurable_const
      ⟨‖z‖, fun _ => le_refl _⟩ = z • 1 := by
  have hUniform : TendstoUniformly
      (fun (_n : ℕ) (t : ℝ) => SimpleFunc.const ℝ z t)
      (fun _t : ℝ => z) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [] with n
    intro t
    change dist z z < ε
    rw [dist_self]
    exact hε
  have hlim := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    (fun _ : ℝ => z) measurable_const ⟨‖z‖, fun _ => le_refl _⟩
    (fun _n => SimpleFunc.const ℝ z) hUniform
  have hconst : Tendsto (fun _n : ℕ => z • (1 : E →L[ℂ] E)) atTop
      (nhds (z • 1)) := tendsto_const_nhds
  apply tendsto_nhds_unique hlim
  simpa only [E_pvm.simpleIntegral_const] using hconst
private theorem PVM.integral_const_mul_local (E_pvm : PVM E)
    (c : ℂ) (f : ℝ → ℂ) (hf : Measurable f)
    (hbddf : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (hbddMul : ∃ C, ∀ r, ‖c * f r‖ ≤ C) :
    E_pvm.integral (fun r => c * f r) (measurable_const.mul hf) hbddMul =
      c • E_pvm.integral f hf hbddf := by
  let fc : ℝ → ℂ := fun _ => c
  have hfc : Measurable fc := measurable_const
  have hbddc : ∃ C, ∀ r, ‖fc r‖ ≤ C := ⟨‖c‖, fun _ => le_refl _⟩
  have hfun : (fun r => c * f r) = fc * f := by
    funext r
    rfl
  calc
    E_pvm.integral (fun r => c * f r) (measurable_const.mul hf) hbddMul =
        E_pvm.integral (fc * f) (hfc.mul hf) hbddMul :=
      E_pvm.integral_congr_local hfun _ _ _ _
    _ = E_pvm.integral fc hfc hbddc * E_pvm.integral f hf hbddf :=
      E_pvm.integral_mul fc f hfc hf hbddc hbddf hbddMul
    _ = c • E_pvm.integral f hf hbddf := by
      rw [show E_pvm.integral fc hfc hbddc = c • 1 by
        exact E_pvm.integral_const_local c, smul_mul_assoc, one_mul]
private theorem stonePhase_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (fun t : ℝ => stonePhase t r) (Complex.I * (r : ℂ)) 0 := by
  have harg : HasDerivAt
      (fun t : ℝ => Complex.I * (t : ℂ) * (r : ℂ))
      (Complex.I * (r : ℂ)) 0 := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt.const_mul Complex.I).mul_const (r : ℂ)
  unfold stonePhase
  simpa only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul]
    using harg.cexp
private theorem stoneQuotient_tendsto (r : ℝ) :
    Tendsto (fun t : ℝ => stoneQuotient t r)
      (nhdsWithin 0 {0}ᶜ) (nhds (r : ℂ)) := by
  have hslope := (stonePhase_hasDerivAt_zero r).tendsto_slope_zero
  have hconst : Tendsto (fun _t : ℝ => (-Complex.I : ℂ))
      (nhdsWithin 0 {0}ᶜ) (nhds (-Complex.I)) := tendsto_const_nhds
  have hscaled := hconst.mul hslope
  convert hscaled using 1
  · funext t
    rw [stoneQuotient, zero_add, Complex.real_smul, Complex.ofReal_inv,
      mul_inv_rev, Complex.inv_I]
    ring
  · congr 1
    rw [neg_mul, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, neg_neg]
private theorem integral_stoneQuotient (E_pvm : PVM E) (t : ℝ) :
    E_pvm.integral (stoneQuotient t) (stoneQuotient_measurable t)
        ⟨‖(Complex.I * (t : ℂ))⁻¹‖ * 2, stoneQuotient_bounded t⟩ =
      (Complex.I * (t : ℂ))⁻¹ •
        (spectralEvolution E_pvm t - spectralEvolution E_pvm 0) := by
  let c : ℂ := (Complex.I * (t : ℂ))⁻¹
  let f : ℝ → ℂ := stonePhase t - stonePhase 0
  have hf : Measurable f := (stonePhase_measurable t).sub (stonePhase_measurable 0)
  have hbddf : ∃ C, ∀ r, ‖f r‖ ≤ C := ⟨2, stonePhase_sub_bounded 0 t⟩
  have hbddMul : ∃ C, ∀ r, ‖c * f r‖ ≤ C :=
    ⟨‖(Complex.I * (t : ℂ))⁻¹‖ * 2, stoneQuotient_bounded t⟩
  have hfun : stoneQuotient t = fun r => c * f r := by
    funext r
    rfl
  calc
    E_pvm.integral (stoneQuotient t) (stoneQuotient_measurable t) hbddMul =
        E_pvm.integral (fun r => c * f r) (measurable_const.mul hf) hbddMul :=
      E_pvm.integral_congr_local hfun _ _ _ _
    _ = c • E_pvm.integral f hf hbddf :=
      E_pvm.integral_const_mul_local c f hf hbddf hbddMul
    _ = c • (spectralEvolution E_pvm t - spectralEvolution E_pvm 0) := by
      rw [spectralEvolution_sub]
private theorem spectralDifferenceQuotient_eq_integral
    (E_pvm : PVM E) (t : ℝ) (x : E) :
    (Complex.I * (t : ℂ))⁻¹ • (spectralEvolution E_pvm t x - x) =
      E_pvm.integral (stoneQuotient t) (stoneQuotient_measurable t)
        ⟨‖(Complex.I * (t : ℂ))⁻¹‖ * 2, stoneQuotient_bounded t⟩ x := by
  rw [integral_stoneQuotient]
  rw [smul_apply, sub_apply, spectralEvolution_zero, one_apply_eq_self]
private theorem stoneQuotient_norm_le (t r : ℝ) (ht : t ≠ 0) :
    ‖stoneQuotient t r‖ ≤ ‖r‖ := by
  have hnum : ‖stonePhase t r - stonePhase 0 r‖ ≤ ‖t * r‖ := by
    rw [stonePhase_zero]
    change ‖Complex.exp (Complex.I * (t : ℂ) * (r : ℂ)) - 1‖ ≤ ‖t * r‖
    rw [mul_assoc, ← Complex.ofReal_mul]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  rw [stoneQuotient, norm_mul]
  calc
    ‖(Complex.I * (t : ℂ))⁻¹‖ * ‖stonePhase t r - stonePhase 0 r‖ ≤
        ‖(Complex.I * (t : ℂ))⁻¹‖ * ‖t * r‖ :=
      mul_le_mul_of_nonneg_left hnum (norm_nonneg _)
    _ = ‖r‖ := by
      rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, norm_mul,
        ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht), one_mul]
private theorem quotientDifference_lintegral_tendsto_zero
    (E_pvm : PVM E)
    (x : (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable).domain) :
    Tendsto
      (fun t : ℝ => ∫⁻ r,
        (↑(‖stoneQuotient t r - (r : ℂ)‖₊ ^ 2) : ENNReal)
          ∂(E_pvm.scalarMeasure (x : E)))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  have hcoordMeas : Measurable
      (fun r : ℝ => (↑(‖(r : ℂ)‖₊ ^ 2) : ENNReal)) :=
    ((Complex.continuous_ofReal.measurable.nnnorm.pow_const 2).coe_nnreal_ennreal)
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (μ := E_pvm.scalarMeasure (x : E))
    (l := nhdsWithin 0 {0}ᶜ)
    (F := fun t r => (↑(‖stoneQuotient t r - (r : ℂ)‖₊ ^ 2) : ENNReal))
    (f := fun _ => 0)
    (fun r => 4 * (↑(‖(r : ℂ)‖₊ ^ 2) : ENNReal))
    (Filter.Eventually.of_forall fun t =>
      (((stoneQuotient_measurable t).sub
        Complex.continuous_ofReal.measurable).nnnorm.pow_const 2).coe_nnreal_ennreal)
    (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply ae_of_all
      intro r
      have ht0 : t ≠ 0 := ht
      have hnorm : ‖stoneQuotient t r - (r : ℂ)‖ ≤ 2 * ‖r‖ := by
        calc
          ‖stoneQuotient t r - (r : ℂ)‖ ≤
              ‖stoneQuotient t r‖ + ‖(r : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖r‖ + ‖r‖ := add_le_add (stoneQuotient_norm_le t r ht0)
            (Complex.norm_real r).le
          _ = 2 * ‖r‖ := by ring
      change ‖stoneQuotient t r - (r : ℂ)‖ₑ ^ 2 ≤
        4 * (↑(‖(r : ℂ)‖₊ ^ 2) : ENNReal)
      calc
        ‖stoneQuotient t r - (r : ℂ)‖ₑ ^ 2 =
            ENNReal.ofReal (‖stoneQuotient t r - (r : ℂ)‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
        _ ≤ ENNReal.ofReal ((2 * ‖r‖) ^ 2) := ENNReal.ofReal_le_ofReal
          ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).2 hnorm)
        _ = 4 * (↑(‖(r : ℂ)‖₊ ^ 2) : ENNReal) := by
          rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg (2 : ℝ)),
            ENNReal.ofReal_pow (norm_nonneg r) 2, Complex.nnnorm_real,
            ENNReal.coe_pow, ← enorm_eq_nnnorm, ← ofReal_norm]
          norm_num)
    (by
      rw [lintegral_const_mul 4 hcoordMeas]
      exact ENNReal.mul_ne_top (by norm_num) x.property.ne)
    (ae_of_all _ fun r => by
      have hconstR : Tendsto (fun _t : ℝ => (r : ℂ)) (nhdsWithin 0 {0}ᶜ)
          (nhds (r : ℂ)) := tendsto_const_nhds
      have hsub := (stoneQuotient_tendsto r).sub hconstR
      have hreal := ENNReal.tendsto_ofReal (hsub.norm.pow 2)
      convert hreal using 1
      · funext t
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
          enorm_eq_nnnorm, ENNReal.coe_pow]
      · rw [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          ENNReal.ofReal_zero])
  simpa only [lintegral_zero] using h
private theorem spectralDifferenceQuotient_tendsto
    (E_pvm : PVM E)
    (x : (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable).domain) :
    Tendsto
      (fun t : ℝ => (Complex.I * (t : ℂ))⁻¹ •
        (spectralEvolution E_pvm t (x : E) - (x : E)))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hIntegral := quotientDifference_lintegral_tendsto_zero E_pvm x
  have hthreshold : 0 < ENNReal.ofReal (ε ^ 2) :=
    ENNReal.ofReal_pos.2 (sq_pos_of_pos hε)
  filter_upwards [hIntegral.eventually (gt_mem_nhds hthreshold)] with t ht
  rw [dist_eq_norm]
  have hL2 := E_pvm.ofReal_norm_sq_integral_sub_unboundedIntegral
    (stoneQuotient t) (stoneQuotient_measurable t)
    ⟨‖(Complex.I * (t : ℂ))⁻¹‖ * 2, stoneQuotient_bounded t⟩
    ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable x
  have hofReal :
      ENNReal.ofReal
          (‖(Complex.I * (t : ℂ))⁻¹ •
            (spectralEvolution E_pvm t (x : E) - (x : E)) -
              E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
                Complex.continuous_ofReal.measurable x‖ ^ 2) <
        ENNReal.ofReal (ε ^ 2) := by
    rw [spectralDifferenceQuotient_eq_integral]
    exact hL2.trans_lt (by simpa only [ENNReal.coe_pow] using ht)
  have hsquare :
      ‖(Complex.I * (t : ℂ))⁻¹ •
          (spectralEvolution E_pvm t (x : E) - (x : E)) -
        E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
          Complex.continuous_ofReal.measurable x‖ ^ 2 < ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hε)).1 hofReal
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 hsquare
private theorem coordinateOperator_le_phaseGenerator (E_pvm : PVM E) :
    E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable ≤
      (spectralUnitaryGroup E_pvm).generator := by
  let A := E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
    Complex.continuous_ofReal.measurable
  let U := spectralUnitaryGroup E_pvm
  have hdomain : A.domain ≤ U.generator.domain := by
    intro x hx
    apply (U.mem_generator_domain_iff x).2
    let xA : A.domain := ⟨x, hx⟩
    refine ⟨A xA, ?_⟩
    exact spectralDifferenceQuotient_tendsto E_pvm xA
  refine ⟨hdomain, ?_⟩
  intro x y hxy
  have hcoord := spectralDifferenceQuotient_tendsto E_pvm x
  have hgenerator := U.tendsto_generator y
  change Tendsto
    (fun t : ℝ => (Complex.I * (t : ℂ))⁻¹ •
      (spectralEvolution E_pvm t (y : E) - (y : E)))
    (nhdsWithin 0 {0}ᶜ) (nhds (U.generator y)) at hgenerator
  rw [← hxy] at hgenerator
  exact tendsto_nhds_unique hcoord hgenerator
private theorem quotientTime_tendsto :
    Tendsto quotientTime atTop (nhdsWithin 0 {0}ᶜ) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  apply Filter.Eventually.of_forall
  intro n
  change quotientTime n ≠ 0
  unfold quotientTime
  positivity
private theorem phaseGenerator_coordinate_integrable (E_pvm : PVM E)
    (x : (spectralUnitaryGroup E_pvm).generator.domain) :
    ∫⁻ r, ‖(r : ℂ)‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) < ⊤ := by
  let U := spectralUnitaryGroup E_pvm
  let q : ℕ → ℝ → ℂ := fun n => stoneQuotient (quotientTime n)
  let L : ENNReal := ENNReal.ofReal (‖U.generator x‖ ^ 2)
  have hquotient : Tendsto
      (fun n => (Complex.I * (quotientTime n : ℂ))⁻¹ •
        (spectralEvolution E_pvm (quotientTime n) (x : E) - (x : E)))
      atTop (nhds (U.generator x)) := by
    have hgenerator := U.tendsto_generator x
    change Tendsto
      (fun t : ℝ => (Complex.I * (t : ℂ))⁻¹ •
        (spectralEvolution E_pvm t (x : E) - (x : E)))
      (nhdsWithin 0 {0}ᶜ) (nhds (U.generator x)) at hgenerator
    exact hgenerator.comp quotientTime_tendsto
  have hnorm : Tendsto
      (fun n => ENNReal.ofReal
        (‖(Complex.I * (quotientTime n : ℂ))⁻¹ •
          (spectralEvolution E_pvm (quotientTime n) (x : E) - (x : E))‖ ^ 2))
      atTop (nhds L) := by
    exact ENNReal.tendsto_ofReal (hquotient.norm.pow 2)
  have hintegrals : Tendsto
      (fun n => ∫⁻ r, (↑(‖q n r‖₊ ^ 2) : ENNReal)
        ∂(E_pvm.scalarMeasure (x : E)))
      atTop (nhds L) := by
    apply hnorm.congr'
    apply Filter.Eventually.of_forall
    intro n
    have hL2 := E_pvm.ofReal_norm_sq_integral
      (stoneQuotient (quotientTime n))
      (stoneQuotient_measurable (quotientTime n))
      ⟨‖(Complex.I * (quotientTime n : ℂ))⁻¹‖ * 2,
        stoneQuotient_bounded (quotientTime n)⟩ (x : E)
    rw [← spectralDifferenceQuotient_eq_integral] at hL2
    simpa only [q, ENNReal.coe_pow] using hL2
  have hpointwise : ∀ r, Tendsto
      (fun n => (↑(‖q n r‖₊ ^ 2) : ENNReal)) atTop
      (nhds (↑(‖(r : ℂ)‖₊ ^ 2) : ENNReal)) := by
    intro r
    have hq := (stoneQuotient_tendsto r).comp quotientTime_tendsto
    have hreal := ENNReal.tendsto_ofReal (hq.norm.pow 2)
    convert hreal using 1
    · funext n
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
        enorm_eq_nnnorm, ENNReal.coe_pow]
      rfl
    · rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
        enorm_eq_nnnorm, ENNReal.coe_pow]
  calc
    ∫⁻ r, ‖(r : ℂ)‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) =
        ∫⁻ r, liminf (fun n => (↑(‖q n r‖₊ ^ 2) : ENNReal)) atTop
          ∂(E_pvm.scalarMeasure (x : E)) := by
      apply lintegral_congr
      intro r
      exact (hpointwise r).liminf_eq.symm
    _ ≤ liminf
        (fun n => ∫⁻ r, (↑(‖q n r‖₊ ^ 2) : ENNReal)
          ∂(E_pvm.scalarMeasure (x : E))) atTop := by
      apply lintegral_liminf_le
      intro n
      exact Measurable.coe_nnreal_ennreal
        ((stoneQuotient_measurable (quotientTime n)).nnnorm.pow_const 2)
    _ = L := hintegrals.liminf_eq
    _ < ⊤ := ENNReal.ofReal_lt_top
private theorem phaseGenerator_domain_le_coordinateOperator (E_pvm : PVM E) :
    (spectralUnitaryGroup E_pvm).generator.domain ≤
      (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable).domain := by
  intro x hx
  rw [E_pvm.mem_domain_unboundedIntegral]
  exact phaseGenerator_coordinate_integrable E_pvm ⟨x, hx⟩
private theorem spectralUnitaryGroup_generator (E_pvm : PVM E) :
    (spectralUnitaryGroup E_pvm).generator =
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable := by
  have hle := coordinateOperator_le_phaseGenerator E_pvm
  have hdomain :
      (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
          Complex.continuous_ofReal.measurable).domain =
        (spectralUnitaryGroup E_pvm).generator.domain :=
    le_antisymm hle.1 (phaseGenerator_domain_le_coordinateOperator E_pvm)
  exact (LinearPMap.eq_of_le_of_domain_eq hle hdomain).symm
end

set_option autoImplicit false
open MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) :
    E_pvm.phaseUnitaryGroup.generator =
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable := by
  simpa only [PVM.phaseUnitaryGroup] using spectralUnitaryGroup_generator E_pvm
end PVM
