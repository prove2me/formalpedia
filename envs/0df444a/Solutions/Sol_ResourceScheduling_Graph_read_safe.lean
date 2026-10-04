-- Prove2me | solution 1 for ResourceScheduling.Graph.read_safe
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:00:04.413621+00:00
-- url     : https://prove2.me/submissions/ef4e4f35-957e-402e-9bef-b142287de89f

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg

theorem solution (a b dst : GraphReg) (h : b ≠ index) (B N : ℕ) (s : RAMState GraphReg)
    (hs : RAMBound B s) (ha : s.val a ≤ N) (hn : s.val n ≤ N) (hb : s.val b ≤ N)
    (hB : N * N + N ≤ B) (hpos : 1 ≤ B) : RAMSafe (GraphProgram.read a b dst h) B s := by
  let z1 := s.val a * s.val n
  let z2 := s.val b + z1
  let s1 := s.set index z1
  let s2 := s.set index z2
  let s3 := s2.set dst (if s.word.getD z2 Letter.sep = Letter.one then 1 else 0)
  have hz1 : z1 ≤ N * N := Nat.mul_le_mul ha hn
  have hs1 : RAMBound B s1 := ram_bound_set B s hs index z1 (by omega)
  have hs2 : RAMBound B s2 := ram_bound_set B s hs index z2 (by dsimp [z2]; omega)
  have hs3 : RAMBound B s3 := ram_bound_set B s2 hs2 dst _ (by split <;> omega)
  simpa [RAMSafe, GraphProgram.read, GraphProgram.block, RAMCode.Bounded, RAMCode.eval,
    s1, s2, s3, z1, z2, RAMState.set, h, Nat.add_comm] using
    (⟨⟨hs, hs1, hs2, hs3⟩, hs3⟩ :
      (RAMBound B s ∧ RAMBound B s1 ∧ RAMBound B s2 ∧ RAMBound B s3) ∧ RAMBound B s3)

#print axioms solution
