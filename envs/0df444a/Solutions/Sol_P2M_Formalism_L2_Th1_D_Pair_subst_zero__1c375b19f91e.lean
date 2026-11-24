-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_D_Pair_subst_zero__1c375b19f91e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:18.842361+00:00
-- url     : https://prove2.me/submissions/cc4b4178-6dcd-4cd0-9ac2-dcbc9ac5bec5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.Pair
theorem _root_.solution {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ) :
    subst φ (0 : MvPowerSeries ι K) = 0 := by
  first
  | exact MvPowerSeries.subst_zero hφ
  | (rw [← coe_substAlgHom hφ]; exact map_zero _)
  | simp
end Formalism.L2.Th1.D.Pair
