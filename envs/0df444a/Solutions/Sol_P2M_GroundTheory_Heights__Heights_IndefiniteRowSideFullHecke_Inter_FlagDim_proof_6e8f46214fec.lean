-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_proof_6e8f46214fec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:20.378976+00:00
-- url     : https://prove2.me/submissions/8dca94d7-c4aa-450c-bd5b-5bb154e032a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_ker_flagMinorMap_eq_bff51324077a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_trdeg_upperQuot_3c97414c0032
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_upperKer_isMultiHomogIdeal_e43b0d28821a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_upperKer_isRelevant_2be07b5131be
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_trdeg


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
open FlagDim
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace FlagDim
theorem _root_.solution : FlagDim.Statement := by
  intro F _ n
  have hker : flagIdealOver F n = upperKer F n := ker_flagMinorMap_eq F n
  rw [hker]
  refine ⟨⟨inferInstance, upperKer_isMultiHomogIdeal F n, upperKer_isRelevant F n⟩, ?_⟩
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, trdeg_upperQuot, Fintype.card_fin,
    Cardinal.toENat_nat]
  rfl
end FlagDim
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
