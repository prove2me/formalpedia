-- Prove2me | solution 1 for P010.P010_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T20:01:09.487207+00:00
-- url     : https://prove2.me/submissions/c6c96ab0-71dc-40ca-af55-db794b6bbd85

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_h_le_of_permutation
public import Theorems.Thm_P010_small_upper_bound
public import Theorems.Thm_P010_P010_h_lower_bound
public import Theorems.Thm_P010_P010_upper_large

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) :
    h n = target n := by
  apply Nat.le_antisymm
  · by_cases hlarge : 12 ≤ n
    · obtain ⟨a, ha, hscore⟩ := P010_upper_large n hlarge
      exact (h_le_of_permutation n a ha).trans hscore
    · obtain ⟨a, ha, hscore⟩ :=
        small_upper_bound n hn (by omega)
      exact (h_le_of_permutation n a ha).trans hscore.le
  · exact P010_h_lower_bound n hn
end P010
