-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordConeArithVar_proof_c88814975c4f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:56:35.308036+00:00
-- url     : https://prove2.me/submissions/e618f6f3-d345-4a04-889d-8f05d4f0db44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_isMultiHomogIdeal_e52032a6c383
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_relevant_99031b883ef8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_horizontal_871a820b28bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_algebraMap_injective_3841fd1427ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_ratioPtL_13ad74b72e74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_birational_7092d53bf062
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_trdeg_ratioField_9fe1258f6587
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTrdeg_proof_69ca55d428ae


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open CoordinateConeArithVar
namespace GroundTheory.Heights₂.Heights
namespace CoordConeArithVar
theorem _root_.solution (hDim : IntDomainDim.Statement) : CoordConeArithVar.Statement := by
  intro K _ ι _ Ω _ _ y c d t hK hc ht htL halg
  have hprime : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have hhor : IsHorizontal (mCoordIdeal y) := horizontal y
  refine ⟨hK, ⟨hprime, isMultiHomogIdeal y, relevant y c hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.proof K ι (ratioField y c) (ratioPtL y c) (birational y c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL y c hc]; exact hhor)
  rw [mCoordIdeal_ratioPtL y c hc, trdeg_ratioField y c d t ht htL halg] at htr
  have hA := hDim (MRing ι ⧸ mCoordIdeal y) (CoordinateConeArithVar.algebraMap_injective _ hhor)
  rw [hA, htr]
  simp only [map_add, map_natCast]
  norm_cast
  omega
end CoordConeArithVar
end GroundTheory.Heights₂.Heights
