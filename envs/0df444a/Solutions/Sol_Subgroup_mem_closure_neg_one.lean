-- Prove2me | solution 1 for Subgroup.mem_closure_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:07.613799+00:00
-- url     : https://prove2.me/submissions/3484f358-f54b-4349-9575-0d1e52f52049

import Mathlib.Algebra.Group.Subgroup.Lattice
import Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Theorems.Thm_P2M_Odd_neg_one_zpow__161a9ee538a7


set_option autoImplicit false

namespace Subgroup
theorem _root_.solution {α : Type*} [Group α] [HasDistribNeg α] {a : α} :
    a ∈ Subgroup.closure {-1} ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro h
    obtain ⟨n, h⟩ := Subgroup.mem_closure_singleton.mp h
    rcases n.even_or_odd with hn | hn
    · left
      simpa [hn.neg_one_zpow] using h.symm
    · right
      simpa [hn.neg_one_zpow'] using h.symm
  · rintro (h | h) <;> simp [h]
end Subgroup
