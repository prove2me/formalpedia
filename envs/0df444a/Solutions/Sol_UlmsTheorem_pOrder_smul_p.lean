-- Prove2me | solution 1 for UlmsTheorem.pOrder_smul_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:21.350409+00:00
-- url     : https://prove2.me/submissions/3eff4a8c-7166-4281-8618-5f5543061fda

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_pOrder_le_succ_of_smul_p_le
public import Theorems.Thm_UlmsTheorem_smul_p_pOrder_le_of_le_succ
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


attribute [local simp] UlmsTheorem.pOrder_zero

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution (x : G) (hx : 0 < pOrder p x) :
    pOrder p (p • x) = pOrder p x - 1 := by
  cases hox : pOrder p x using ENat.recTopCoe with
  | top =>
      simpa [hox] using show pOrder p (p • x) = ⊤ from by
        by_contra hy
        rcases WithTop.ne_top_iff_exists.mp hy with ⟨n, hn⟩
        have hxle : pOrder p x ≤ n + 1 :=
          pOrder_le_succ_of_smul_p_le p (by rw [← hn]; exact le_rfl)
        rw [hox] at hxle
        exact (WithTop.not_top_le_coe (n + 1) hxle).elim
  | coe n =>
      cases n with
      | zero =>
          simp [hox] at hx
      | succ n =>
          have hupper : pOrder p (p • x) ≤ n :=
            smul_p_pOrder_le_of_le_succ p (by simp [hox])
          cases n with
          | zero =>
              exact le_antisymm hupper bot_le
          | succ m =>
              apply le_antisymm hupper
              by_contra hlow
              have hlt : pOrder p (p • x) < m + 1 := lt_of_not_ge hlow
              have hle : pOrder p (p • x) ≤ m := by
                simpa [Nat.succ_eq_add_one] using
                  (ENat.lt_natCast_add_one_iff (m := pOrder p (p • x)) (n := m)).1 hlt
              have hxle : pOrder p x ≤ m + 1 := pOrder_le_succ_of_smul_p_le p hle
              rw [hox] at hxle
              exact (not_le_of_gt <| by
                simpa using
                  (ENat.lt_natCast_add_one_iff (m := (m : ℕ∞)) (n := m)).2 le_rfl) hxle |>.elim
end UlmsTheorem
