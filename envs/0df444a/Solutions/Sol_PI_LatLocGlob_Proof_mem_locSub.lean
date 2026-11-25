-- Prove2me | solution 1 for PI.LatLocGlob.Proof.mem_locSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:25.073637+00:00
-- url     : https://prove2.me/submissions/3c044551-bba2-4784-a8e1-4e7c6636d541

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Lemmata_GeneralBFactThirdBisAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LatLocGlob PI.LatLocGlob.Proof
open PI.LatLocGlob
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
namespace PI.LatLocGlob.Proof
theorem _root_.solution {p : Ideal R} {hp : p.IsPrime} {N : Submodule R V} {x : V} :
    x ∈ locSub p hp N ↔ x ∈ loc p N := Iff.rfl
end PI.LatLocGlob.Proof
