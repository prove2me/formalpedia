-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_B_Map_map_psubst__d587dd5fe1df
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:42.696003+00:00
-- url     : https://prove2.me/submissions/3f632337-0038-4673-8c6b-c9353bcf172d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_psubst

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
theorem _root_.solution {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    PowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (PowerSeries.map j a) (PowerSeries.map j f) :=
  map_psubst j (ι := Unit) ha f
end Formalism.L2.Th1.B.Map
