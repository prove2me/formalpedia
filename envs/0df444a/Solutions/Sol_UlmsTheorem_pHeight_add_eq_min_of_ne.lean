-- Prove2me | solution 1 for UlmsTheorem.pHeight_add_eq_min_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:49.800201+00:00
-- url     : https://prove2.me/submissions/43825a3b-9760-4ed8-aa5a-6851b508d0bc

module
public import Mathlib.Data.ENat.Lattice
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Theorems.Thm_UlmsTheorem_pHeight_ge_iff
public import Theorems.Thm_UlmsTheorem_pHeight_add_ge_min

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (x y : G) (h : pHeight p x ≠ pHeight p y) :
    pHeight p (x + y) = min (pHeight p x) (pHeight p y) := by
  wlog hx_lt_hy : pHeight p x < pHeight p y generalizing x y
  · rw [add_comm, this y x h.symm (lt_of_le_of_ne (le_of_not_gt hx_lt_hy) h.symm)]
    exact min_comm _ _
  have hle : pHeight p (x + y) ≤ pHeight p x := by
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℕ∞) = pHeight p x :=
      WithTop.ne_top_iff_exists.mp (ne_top_of_lt hx_lt_hy)
    have hk_lt_y  : (k : ℕ∞) < pHeight p y       := by rw [hk]; exact hx_lt_hy
    have hk_lt_xy : (k : ℕ∞) < pHeight p (x + y) := by rw [hk]; exact hlt
    have succ_le : ∀ a : ℕ∞, (k : ℕ∞) < a → (↑(k + 1) : ℕ∞) ≤ a := fun a ha ↦ by
      rcases a with (_ | m)
      · exact le_top
      · exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp ha))
    obtain ⟨zy, hzy⟩ := (pHeight_ge_iff p y (k + 1)).mp (succ_le _ hk_lt_y)
    obtain ⟨zxy, hzxy⟩ := (pHeight_ge_iff p (x + y) (k + 1)).mp (succ_le _ hk_lt_xy)
    have hx_mem : (↑(k + 1) : ℕ∞) ≤ pHeight p x :=
      (pHeight_ge_iff p x (k + 1)).mpr
        ⟨zxy - zy, by rw [smul_sub, hzxy, hzy, add_sub_cancel_right]⟩
    rw [← hk] at hx_mem
    exact absurd (WithTop.coe_le_coe.mp hx_mem) (by omega)
  exact le_antisymm (le_min hle (le_trans hle hx_lt_hy.le)) (pHeight_add_ge_min p x y)
end UlmsTheorem
