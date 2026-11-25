-- Prove2me | solution 1 for PI.LatLocGlob.Proof.mem_loc_of_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:46.212653+00:00
-- url     : https://prove2.me/submissions/fdcd3ea5-0f51-4101-8698-9669594b6c82

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
theorem _root_.solution {p : Ideal R} (hp : p.IsPrime) {N : Submodule R V} {u : R} {y : V}
    (hu : u ∉ p) (h : u • y ∈ loc p N) : y ∈ loc p N := by
  obtain ⟨s, hs, hsy⟩ := mem_loc.1 h
  exact mem_loc.2 ⟨s * u, fun h' => (hp.mem_or_mem h').elim hs hu, by rwa [mul_smul]⟩
end PI.LatLocGlob.Proof
