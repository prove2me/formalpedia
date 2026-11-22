-- Prove2me | solution 1 for Parikh.image_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:12.321994+00:00
-- url     : https://prove2.me/submissions/2f6fc566-36c0-43e6-a58c-4ad9d62550c3

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_counts_append


set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [DecidableEq T] (L M : Language T) :
    image (L * M) = image L + image M := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu, z, hz, rfl⟩ := Language.mem_mul.mp hw
    exact Set.mem_add.mpr ⟨counts u, ⟨u, hu, rfl⟩, counts z,
      ⟨z, hz, rfl⟩, (counts_append u z).symm⟩
  · intro hv
    obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩ := Set.mem_add.mp hv
    exact ⟨u ++ z, Language.append_mem_mul hu hz, counts_append u z⟩
end Parikh
