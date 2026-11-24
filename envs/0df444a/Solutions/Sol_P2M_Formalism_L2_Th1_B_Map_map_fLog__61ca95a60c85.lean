-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_B_Map_map_fLog__61ca95a60c85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:40:14.211007+00:00
-- url     : https://prove2.me/submissions/5bf87422-2b3c-4e23-b6ca-fdf86197c23f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_fLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Map
open Formalism.InvariantFactorPaths.G7 (at1 cob)
variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
namespace Formalism.L2.Th1.B.Map
theorem _root_.solution {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 1) :
    PowerSeries.map j (fLog a) = fLog (PowerSeries.map j a) :=
  map_fLog j (ι := Unit) ha
end Formalism.L2.Th1.B.Map
