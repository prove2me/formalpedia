-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_B_Map_map_fExp__32d85cf1f169
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:03.764799+00:00
-- url     : https://prove2.me/submissions/2aae0449-54f4-41c1-a1fc-70ed72bb31e4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_fExp

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
theorem _root_.solution {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.map j (fExp a) = fExp (PowerSeries.map j a) :=
  map_fExp j (ι := Unit) ha
end Formalism.L2.Th1.B.Map
