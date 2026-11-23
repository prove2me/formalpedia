-- Prove2me | solution 1 for PI.Dv.ProjAW.mem_cutE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:19.979798+00:00
-- url     : https://prove2.me/submissions/0827a674-f6cd-4fa8-92e5-8abb4afd8edb

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
theorem _root_.solution (f : Module.End K A.V) (M : Submodule (𝓞 K) A.V) (x : A.V) :
    x ∈ cutE A f M ↔ x ∈ M ∧ x ∈ LinearMap.range f := Iff.rfl
end PI.Dv.ProjAW
