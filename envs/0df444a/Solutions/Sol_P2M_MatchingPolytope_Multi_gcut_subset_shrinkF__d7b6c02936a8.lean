-- Prove2me | solution 1 for P2M_MatchingPolytope_Multi_gcut_subset_shrinkF__d7b6c02936a8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:30.708709+00:00
-- url     : https://prove2.me/submissions/62f0af0b-8378-4453-bcb0-eb31bbea32a5

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
public import Theorems.Thm_MatchingPolytope_Multi_mem_shrinkF


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [DecidableEq V]
namespace MatchingPolytope.Multi
theorem _root_.solution (S : Finset V) :
    gcut ends F S ⊆ shrinkF ends F (W \ S) := by
  intro e he
  simp only [gcut, Finset.mem_filter] at he
  obtain ⟨heF, ⟨u, hu, huS⟩, -⟩ := he
  exact mem_shrinkF.2 ⟨heF, u, hu, fun h => (Finset.mem_sdiff.1 h).2 huS⟩
end MatchingPolytope.Multi
