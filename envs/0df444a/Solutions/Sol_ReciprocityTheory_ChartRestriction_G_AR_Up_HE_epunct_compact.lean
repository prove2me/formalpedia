-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.HE.epunct_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:25:38.50617+00:00
-- url     : https://prove2.me/submissions/95c8f950-65f0-4380-b17e-d22a37d927cc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_log_gap_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.HE
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate Matrix
noncomputable section
variable {n : ℕ}
variable {U : Set (V n)}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE
theorem _root_.solution (hU : IsOpen U) {e : V n → ℝ} (he : ContDiffOn ℝ ∞ e U)
    (hec : ∀ a, IsCompact {y | y ∈ U ∧ e y ≤ a}) (he0 : ∀ y ∈ U, 0 ≤ e y)
    {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) (a : ℝ) :
    IsCompact {y | y ∈ {y | y ∈ U ∧ g y ≠ 0} ∧ epunct e g y ≤ a} := by
  let K : Set (V n) := {y | y ∈ U ∧ e y ≤ a}
  let K1 : Set (V n) := K ∩ (fun y => Real.exp a * Complex.normSq (g y)) ⁻¹' Set.Ici 1
  let K2 : Set (V n) := K1 ∩ (epunct e g) ⁻¹' Set.Iic a
  have hK : IsCompact K := hec a
  have hc1 : ContinuousOn (fun y => Real.exp a * Complex.normSq (g y)) K :=
    continuousOn_const.mul
      (Complex.continuous_normSq.comp_continuousOn (hg.continuousOn.mono fun y hy => hy.1))
  have hK1 : IsClosed K1 := hc1.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici
  have hcont : ContinuousOn (epunct e g) K1 := by
    intro y hy
    have hyU : y ∈ U := hy.1.1
    have hN : Complex.normSq (g y) ≠ 0 := by
      intro h0
      have h2 : (1 : ℝ) ≤ Real.exp a * Complex.normSq (g y) := hy.2
      rw [h0, mul_zero] at h2
      linarith
    have hgc : ContinuousAt g y := (hg.differentiableAt (hU.mem_nhds hyU)).continuousAt
    have hNc : ContinuousAt (fun w => Complex.normSq (g w)) y :=
      Complex.continuous_normSq.continuousAt.comp hgc
    have hec' : ContinuousAt e y := (he.contDiffAt (hU.mem_nhds hyU)).continuousAt
    have h1 : (1 : ℝ) + Complex.normSq (g y) ≠ 0 := by
      have h0 := Complex.normSq_nonneg (g y)
      have h1 : (0 : ℝ) < 1 + Complex.normSq (g y) := by linarith
      exact h1.ne'
    exact (hec'.add (((continuousAt_const.add hNc).log h1).sub (hNc.log hN))).continuousWithinAt
  have hK2 : IsClosed K2 := hcont.preimage_isClosed_of_isClosed hK1 isClosed_Iic
  have heq : {y | y ∈ {y | y ∈ U ∧ g y ≠ 0} ∧ epunct e g y ≤ a} = K2 := by
    ext y
    constructor
    · rintro ⟨⟨hyU, hgy⟩, hya⟩
      have hNpos : 0 < Complex.normSq (g y) := Complex.normSq_pos.mpr hgy
      have hgap := log_gap_pos hNpos
      have he0y := he0 y hyU
      have hdef : epunct e g y = e y + (Real.log (1 + Complex.normSq (g y)) -
          Real.log (Complex.normSq (g y))) := rfl
      have hya' : epunct e g y ≤ a := hya
      refine ⟨⟨⟨hyU, by linarith⟩, ?_⟩, hya⟩
      show 1 ≤ Real.exp a * Complex.normSq (g y)
      have h1 : Real.log (1 + Complex.normSq (g y)) ≤ a + Real.log (Complex.normSq (g y)) := by
        linarith
      rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add, Real.exp_log hNpos] at h1
      linarith
    · rintro ⟨⟨⟨hyU, -⟩, hy1⟩, hya⟩
      refine ⟨⟨hyU, ?_⟩, hya⟩
      intro h0
      have h2 : (1 : ℝ) ≤ Real.exp a * Complex.normSq (g y) := hy1
      rw [h0, Complex.normSq_zero, mul_zero] at h2
      linarith
  rw [heq]
  exact hK.of_isClosed_subset hK2 (fun y hy => hy.1.1)
end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
