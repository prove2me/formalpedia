-- Prove2me | solution 1 for PI.LatLocGlob.Proof.mem_loc_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:27.996602+00:00
-- url     : https://prove2.me/submissions/891aebb9-26ca-4e29-aa32-76015e297471

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
theorem _root_.solution {p : Ideal R} (hp : p ≠ ⊤) {N : Submodule R V} {x : V} (hx : x ∈ N) :
    x ∈ loc p N :=
  mem_loc.2 ⟨1, (Ideal.ne_top_iff_one p).1 hp, by simpa using hx⟩
end PI.LatLocGlob.Proof
