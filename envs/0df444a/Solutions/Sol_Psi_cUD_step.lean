-- Prove2me | solution 1 for Psi.cUD_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:41:37.627815+00:00
-- url     : https://prove2.me/submissions/d2afbfe0-d125-4196-804f-d410fb7c4cda

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_cUDraw_fUD_append
import Theorems.Thm_Psi_cUDraw_true_head

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (ρ ρ' : List Bool) (hb : 1 ≤ b)
    (hρU : ρ = [] ∨ ρ.head? = some true) :
    cUD ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
          ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') = a := by
  set L := ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ' with hL
  have hLhead : L.head? = some true := by
    rcases hρU with h | h
    · subst h
      simp only [hL, List.nil_append]
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [List.replicate_succ]; rfl
    · cases ρ with
      | nil => simp at h
      | cons x xs =>
          simp only [List.head?_cons, Option.some.injEq] at h; subst h
          simp only [hL, List.cons_append, List.head?_cons]
  have hcr : cUDraw ((List.replicate a [true, false]).flatten ++ [true] ++ L) = a := by
    have hassoc : (List.replicate a [true, false]).flatten ++ [true] ++ L
        = (List.replicate a [true, false]).flatten ++ (true :: L) := by simp [List.append_assoc]
    rw [hassoc, cUDraw_fUD_append, cUDraw_true_head L hLhead, Nat.add_zero]
  rw [show (List.replicate a [true, false]).flatten ++ [true] ++ ρ
          ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ'
        = (List.replicate a [true, false]).flatten ++ [true] ++ L from by
        simp [hL, List.append_assoc]]
  rw [cUD, hcr, if_neg (by simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]; omega)]
end Psi
