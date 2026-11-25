-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_D_MeanSimeq_of__1ab23f239698
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:25.345535+00:00
-- url     : https://prove2.me/submissions/b0178fc3-000a-40da-8d3c-c26ebfca757b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_shiftType_zXY
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_Formalism_L2_Th1_D_frobenius_square


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries
open Pair TranslateJetMomentLawAnyIdempotentLevel
namespace Formalism.L2.Th1.D
theorem _root_.solution (hM : MeanSimeqL) (hB : BeTilXY) (hLS : LetterShift) : MeanSimeq := by
  intro K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms hO hT ζ hζ
  have hball := (frobenius_square K l σ hU).2
  refine ⟨hM K l d σ hU hd2 hd F hF be0 hF1 hF2 ι om oms hO hT ζ hζ (ZMod d) _
    (hLS K l d σ hU.1).2.1, ?_⟩
  have h := hM K l d σ hU hd2 hd F hF be0 hF1 hF2 ι om oms hO hT ζ hζ (Bool × ι) _
    (shiftType_zXY hU.1 hd hball hO)
  rw [hB K l d σ hU.1.two_le hd be0 ι om oms hO.2 hT] at h
  exact h
end Formalism.L2.Th1.D
