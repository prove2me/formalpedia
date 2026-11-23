-- Prove2me | solution 1 for PI.Dv.ProjAW.fg_img
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:15.548093+00:00
-- url     : https://prove2.me/submissions/4e4eb33c-0377-4520-9278-49ef95c8d538

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution (hG : A.Good) (f : Module.End K A.V) : (imgE A f A.L).FG := hG.2.1.map _
end PI.Dv.ProjAW
