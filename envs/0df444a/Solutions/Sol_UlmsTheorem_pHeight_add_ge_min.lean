-- Prove2me | solution 1 for UlmsTheorem.pHeight_add_ge_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:57:42.654464+00:00
-- url     : https://prove2.me/submissions/df330113-a81d-4182-9495-90b2e09357ac

module
public import Mathlib.Data.ENat.Lattice
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pHeight_ge_iff
public import Theorems.Thm_UlmsTheorem_pHeight_add_ge
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
theorem _root_.solution (x y : G) :
    min (pHeight p x) (pHeight p y) ≤ pHeight p (x + y) := by
  by_cases hxy : pHeight p x ≥ pHeight p y
  · have hxy_in_pnG : ∀ n : ℕ, (n : ℕ∞) ≤ pHeight p y → ∃ z : G, p ^ n • z = x + y := by
      intro n hn
      obtain ⟨zx, hzx⟩ := (pHeight_ge_iff p x n).1 (le_trans hn hxy)
      obtain ⟨zy, hzy⟩ := (pHeight_ge_iff p y n).1 hn
      exact ⟨zx + zy, by rw [smul_add, hzx, hzy]⟩
    contrapose! hxy_in_pnG with hxy_not_in_pnG
    rw [min_eq_right hxy] at hxy_not_in_pnG
    obtain ⟨n, hn₁, hn₂⟩ : ∃ n : ℕ, (n : ℕ∞) ≤ pHeight p y ∧ (n : ℕ∞) > pHeight p (x + y) := by
      obtain ⟨n, hn, hnlt⟩ := WithTop.lt_iff_exists_coe.mp hxy_not_in_pnG
      refine ⟨n + 1, ENat.natCast_add_one_le_iff.mpr hnlt, ?_⟩
      rw [hn]
      exact ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self n)
    exact ⟨n, hn₁,
      fun z hz ↦ (not_le.mpr hn₂) ((pHeight_ge_iff p (x + y) n).2 ⟨z, hz⟩)⟩
  · have h_subadd : ∀ n : ℕ, (n : ℕ∞) ≤ pHeight p x → (n : ℕ∞) ≤ pHeight p (x + y) := fun n hn ↦
      pHeight_add_ge p x y n hn (le_trans hn (le_of_not_ge hxy))
    cases h : pHeight p x <;> aesop
end UlmsTheorem
