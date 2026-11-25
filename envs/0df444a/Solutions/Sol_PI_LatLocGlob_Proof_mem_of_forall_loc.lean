-- Prove2me | solution 1 for PI.LatLocGlob.Proof.mem_of_forall_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:49.579141+00:00
-- url     : https://prove2.me/submissions/b40afbb3-8405-4b49-99fd-1a181299be80

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
theorem _root_.solution (N : Submodule R V) (x : V)
    (h : ∀ p : Ideal R, p.IsMaximal → x ∈ loc p N) : x ∈ N := by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R V x)
  have hI : ∀ r, r ∈ I ↔ r • x ∈ N := fun r => by simp [I]
  by_cases htop : I = ⊤
  · have h1 : (1 : R) ∈ I := by rw [htop]; exact Submodule.mem_top
    simpa using (hI 1).1 h1
  · obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I htop
    obtain ⟨s, hs, hsx⟩ := mem_loc.1 (h p hp)
    exact absurd (hIp ((hI s).2 hsx)) hs
end PI.LatLocGlob.Proof
