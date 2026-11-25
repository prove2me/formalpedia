-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_exXi_h_bce7dc8fca97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:33:42.684206+00:00
-- url     : https://prove2.me/submissions/a72db80f-5c9a-4f40-b783-913760e42d71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ofMetrics_fs_h_bd4ac42ff7dd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumY_base_9953fcac61b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumY_det_0c73e0eee300
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumY_line_4a9ef4c8296c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_prod_YBlk_e84c3fe06e16

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (w : (Σ k, ExY k) → ℂ) :
    exXi.h w = ‖w ⟨.base, ()⟩‖ ^ 3 * ‖w ⟨.det, ()⟩‖⁻¹ *
      (‖w ⟨.line, Sum.inl ()⟩‖ ^ 2 + ‖w ⟨.line, Sum.inr ()⟩‖ ^ 2)⁻¹ := by
  rw [exXi, ofMetrics_fs_h, prod_YBlk, sumY_base, sumY_det, sumY_line]
  simp only [T.twoXiDegY]
  have h1 : Real.sqrt (‖w ⟨.base, ()⟩‖ ^ 2) = ‖w ⟨.base, ()⟩‖ := Real.sqrt_sq (norm_nonneg _)
  have h2 : Real.sqrt (‖w ⟨.det, ()⟩‖ ^ 2) = ‖w ⟨.det, ()⟩‖ := Real.sqrt_sq (norm_nonneg _)
  have h3 : Real.sqrt (‖w ⟨.line, Sum.inl ()⟩‖ ^ 2 + ‖w ⟨.line, Sum.inr ()⟩‖ ^ 2) ^ (-2 : ℤ) =
      (‖w ⟨.line, Sum.inl ()⟩‖ ^ 2 + ‖w ⟨.line, Sum.inr ()⟩‖ ^ 2)⁻¹ := by
    rw [_root_.zpow_neg, zpow_two, Real.mul_self_sqrt (by positivity)]
  rw [h1, h2, h3]
  simp [_root_.zpow_neg, mul_assoc]
end GroundTheory.Heights₂.Heights.Inter
