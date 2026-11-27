-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.HE.epunct_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:32:08.139249+00:00
-- url     : https://prove2.me/submissions/431e30c6-0aa6-4631-9d7c-ad916ad7116a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_two_le_inf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_levi_logNormSq_zero_at
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_isOpen_punct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_contDiffAt_of_punct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_epunct_parts
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lseV


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
    (hel : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re)
    {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) :
    ∀ y ∈ {y | y ∈ U ∧ g y ≠ 0}, ∀ ξ : Fin n → ℂ,
      0 ≤ (leviV n (fun w => (epunct e g w : ℂ)) y ξ).re := by
  intro y hy ξ
  have hU' := isOpen_punct hU hg
  obtain ⟨h1, h2, h3⟩ := epunct_parts hU he hg hy.1 hy.2
  have h12 := h1.of_le two_le_inf
  have h22 := h2.of_le two_le_inf
  have h32 := h3.of_le two_le_inf
  have hsplit : leviV n (fun w => (epunct e g w : ℂ)) y ξ =
      leviV n (fun w => (e w : ℂ)) y ξ +
        (leviV n (fun w => (Real.log (1 + Complex.normSq (g w)) : ℂ)) y ξ +
          (-1 : ℝ) * leviV n (fun w => (Real.log (Complex.normSq (g w)) : ℂ)) y ξ) := by
    have e1 : (fun w => (epunct e g w : ℂ)) = fun w => ((e w +
        (Real.log (1 + Complex.normSq (g w)) + (-1) * Real.log (Complex.normSq (g w))) : ℝ) : ℂ) := by
      funext w; simp only [epunct]; push_cast; ring
    rw [e1, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h12 (h22.add (contDiffAt_const.mul h32)),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add h22 (contDiffAt_const.mul h32),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) h32]
  rw [hsplit, levi_logNormSq_zero_at g y ((contDiffAt_of_punct hU hg hy.1).of_le two_le_inf) hy.2 ξ]
  have hlse := lseV n 2 _ (fun i : Fin 2 => ![fun _ => Complex.normSq (1 : ℂ), fun w => Complex.normSq (g w)] i) hU'
    (fun i => Or.inr (by
      fin_cases i
      · exact ⟨fun _ => 1, contDiffOn_const, fun _ _ => rfl⟩
      · exact ⟨g, ((contDiffOn_of_differentiableOn n g U hU hg).of_le two_le_inf).mono
          (fun w hw => hw.1), fun _ _ => rfl⟩))
    (fun w _ => by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_one]
      linarith [Complex.normSq_nonneg (g w)]) y hy ξ
  have e2 : (fun w => ((Real.log (∑ i : Fin 2, ![fun _ => Complex.normSq (1 : ℂ),
      fun w => Complex.normSq (g w)] i w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + Complex.normSq (g w)) : ℝ) : ℂ) := by
    funext w; simp [Fin.sum_univ_two]
  rw [e2] at hlse
  simp only [mul_zero, add_zero, Complex.add_re]
  exact add_nonneg (hel y hy.1 ξ) hlse
end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
