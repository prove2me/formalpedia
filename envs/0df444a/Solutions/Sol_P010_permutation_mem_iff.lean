-- Prove2me | solution 1 for P010.permutation_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:32:39.909177+00:00
-- url     : https://prove2.me/submissions/144f7c66-aaaa-406e-a3e5-1fcdbfe6eec4

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (a : List ℕ)
    (ha : IsPermutation n a) (x : ℕ) :
    x ∈ a ↔ 1 ≤ x ∧ x ≤ n := by
  change a.Perm (List.range' 1 n) at ha
  rw [ha.mem_iff]
  constructor
  · intro hx
    obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hx
    omega
  · rintro ⟨hpos, hle⟩
    apply List.mem_range'.mpr
    refine ⟨x - 1, by omega, ?_⟩
    omega
end P010
