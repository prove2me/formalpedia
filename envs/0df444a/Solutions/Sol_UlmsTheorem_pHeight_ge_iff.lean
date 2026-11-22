-- Prove2me | solution 1 for UlmsTheorem.pHeight_ge_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:55:13.725833+00:00
-- url     : https://prove2.me/submissions/5a31368a-8522-40aa-9e3d-a88cdc07ade4

module
public import Mathlib.Data.ENat.Lattice
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


attribute [local simp] UlmsTheorem.pHeight_zero

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (x : G) (n : ℕ) :
    (n : ℕ∞) ≤ pHeight p x ↔ ∃ y : G, p ^ n • y = x := by
  by_cases hx : x = 0
  · subst hx
    simp only [pHeight_zero, le_top, true_iff]
    exact ⟨0, smul_zero _⟩
  · simp only [pHeight, if_neg hx]
    constructor
    · intro h
      contrapose! h
      refine lt_of_le_of_lt (csSup_le (a := (↑(n - 1) : ℕ∞)) ?_ ?_) ?_
      · exact ⟨_, ⟨0, ⟨x, by simp +decide⟩, rfl⟩⟩
      · rintro _ ⟨m, ⟨y, hy⟩, rfl⟩
        exact WithTop.coe_le_coe.mpr (Nat.le_sub_one_of_lt (lt_of_not_ge fun hnm ↦
          h (p ^ (m - n) • y) <| by rw [← mul_smul, ← pow_add, Nat.add_sub_of_le hnm, hy]))
      · rcases n with _ | n
        · exact (h x (by simp)).elim
        · simp_all +decide only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
          exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self _)
    · intro ⟨y, hy⟩
      apply le_sSup
      exact ⟨n, ⟨y, hy⟩, rfl⟩
end UlmsTheorem
