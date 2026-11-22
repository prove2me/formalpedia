-- Prove2me | solution 1 for Stable.coincidenceFree_ges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:15:01.107815+00:00
-- url     : https://prove2.me/submissions/0fddd4ce-6620-4b98-a208-4273022b4ab6

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_GES_isConf_rank_lt


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (G : GES L) : CoincidenceFree G.toFamily := by
  intro c hc x y hx hy hne
  rcases lt_or_ge (G.rank c y) (G.rank c x) with hlt | hge
  · refine ⟨{z ∈ c | G.rank c z < G.rank c y} ∪ {y}, GES.isConf_rank_lt G hc hy, ?_, ?_⟩
    · rintro z (hz | hz)
      · exact hz.1
      · exact (Set.mem_singleton_iff.mp hz) ▸ hy
    · constructor
      · rintro (hz | hz)
        · exact absurd hz.2 (by omega)
        · exact absurd (Set.mem_singleton_iff.mp hz) hne
      · intro hz
        exact absurd (Or.inr rfl) hz
  · refine ⟨{z ∈ c | G.rank c z < G.rank c x} ∪ {x}, GES.isConf_rank_lt G hc hx, ?_, ?_⟩
    · rintro z (hz | hz)
      · exact hz.1
      · exact (Set.mem_singleton_iff.mp hz) ▸ hx
    · refine ⟨fun _ => ?_, fun _ => Or.inr rfl⟩
      rintro (hz | hz)
      · exact absurd hz.2 (by omega)
      · exact hne (Set.mem_singleton_iff.mp hz).symm
end Stable
