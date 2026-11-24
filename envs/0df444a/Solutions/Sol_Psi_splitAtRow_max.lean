-- Prove2me | solution 1 for Psi.splitAtRow_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:42:27.489139+00:00
-- url     : https://prove2.me/submissions/5442d1e4-e125-40fd-93b9-14cb206deb34

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_splitAtRow_fst_ne_nil
import Theorems.Thm_Psi_splitAtRow_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1.getLast? ≠ some true ∨ (splitAtRow p h).2.head? ≠ some false := by
  fun_induction splitAtRow p h with
  | case1 p => left; simp
  | case2 h => left; simp
  | case3 rest => left; simp
  | case4 rest hx =>
      right
      cases rest with
      | nil => simp
      | cons b u => cases b with
        | false => exact (hx u rfl).elim
        | true => simp
  | case5 rest h ρ ρ' heq ih =>
      rw [heq] at ih; dsimp only at ih ⊢
      by_cases hρ : ρ = []
      · right
        have hr : rest = [] := by
          by_contra hc
          exact splitAtRow_fst_ne_nil rest (h + 1) (by omega) hc (by rw [heq]; exact hρ)
        have h2 : ρ' = [] := by
          have h3 := splitAtRow_append rest (h + 1)
          rw [heq, hr] at h3; exact (List.append_eq_nil_iff.mp h3).2
        rw [h2]; simp
      · rcases ih with hL | hR
        · left
          obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hρ
          rw [List.getLast?_cons_cons]; exact hL
        · right; exact hR
  | case6 rest h ρ ρ' heq ih =>
      rw [heq] at ih; dsimp only at ih ⊢
      rcases ih with hL | hR
      · left
        by_cases hρ : ρ = []
        · subst hρ; simp
        · obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hρ
          rw [List.getLast?_cons_cons]; exact hL
      · right; exact hR
end Psi
