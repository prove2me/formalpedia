-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeSheetArea_proof_67a75eb12888
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:44.272645+00:00
-- url     : https://prove2.me/submissions/02f42edb-6457-4497-9391-6a21b577507e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramVol_nonneg_7dddc6a166b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mul_setIntegral_eq_of_lintegral_5f5cb8ed0534
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordBall_mass_6af667653fce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_of_isArithVar_pblk_fb6970ea00bb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)
open scoped ENNReal ComplexOrder
namespace GroundTheory.Heights₂.Heights
namespace ConeSheetArea
theorem _root_.solution (h : ConeSheetAreaLintegral.Statement) : ConeSheetArea.Statement := by
  intro n e S hS P Ψ f hP hΨ hf
  obtain ⟨hb0, -⟩ := coordBall_mass (n := n) (m := e + 1) (le_of_isArithVar_pblk hP)
  exact mul_setIntegral_eq_of_lintegral
    (fun x => ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite Unit (PBlk n) P e Ψ hP hΨ x)
    (fun x w => WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩))
    (fun x w t => ‖t‖ ^ (2 * e) *
      gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)
    (fun x w t => mul_nonneg (pow_nonneg (norm_nonneg t) _) (gramVol_nonneg _ x))
    (fun x w => (continuous_norm.pow _).mul continuous_const)
    (by positivity) hb0.ne' (fun F hF => h n e S hS P Ψ F hP hΨ hF) hf
end ConeSheetArea
end GroundTheory.Heights₂.Heights
