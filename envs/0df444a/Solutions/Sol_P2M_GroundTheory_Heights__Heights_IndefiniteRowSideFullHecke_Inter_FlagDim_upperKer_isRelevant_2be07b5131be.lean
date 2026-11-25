-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_upperKer_isRelevant_2be07b5131be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:53:23.844102+00:00
-- url     : https://prove2.me/submissions/4634480e-e19b-4d5b-8274-d4758520492e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_toUpper_flagMinorMap_X_200458d87616
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_flagMinor_uMat_colSet_7757b14e6865
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_succ_7d2c690099e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_ne_zero_7de1111daeff

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution (F : Type) [Field F] (n : ℕ) : IsRelevant (upperKer F n) := by
  intro j
  have hj := j.2
  refine ⟨⟨colSet j.val ⟨j.val, by omega⟩, colSet_card j.val _ le_rfl⟩, ?_⟩
  rw [RingHom.mem_ker, toUpper_flagMinorMap_X]
  simp only
  rw [flagMinor_uMat_colSet F j ⟨j.val, by omega⟩ le_rfl]
  have e : (∏ k : Fin j.val, uMat F n ⟨k.val, by omega⟩ ⟨k.val, by omega⟩) * uMat F n ⟨j.val, by omega⟩ ⟨j.val, by omega⟩ =
      diagProd F n (j.val + 1) (by omega) := (diagProd_succ F n j.val (by omega)).symm
  rw [e]
  exact diagProd_ne_zero F n _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
