-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointVertRAux_degC_eq_finrank_02d1f9d69ae7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:11:43.161267+00:00
-- url     : https://prove2.me/submissions/c24b5a91-87fe-4460-8367-3fefe24e404d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointVertR
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_full_25668629ca13


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.PointVertRAux
namespace GroundTheory.Heights₂.Heights.PointVertRAux
theorem _root_.solution {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K']
    {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) :
    degC (mCoordIdeal y) = Module.finrank ℚ (blockFnField y) := by
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP, Nat.card_eq_fintype_card,
    AlgHom.card]
end GroundTheory.Heights₂.Heights.PointVertRAux
