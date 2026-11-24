-- Prove2me | solution 1 for Psi.hasDD_of_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:45:50.745895+00:00
-- url     : https://prove2.me/submissions/c63876bc-feef-4c80-be9e-925400a1f46e

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_firstDDidx_ff
import Theorems.Thm_Psi_firstDDidx_ft
import Theorems.Thm_Psi_firstDDidx_true
import Theorems.Thm_Psi_hasDD_cons


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l : List Bool) (hn : firstDDidx l = none) : hasDD l = false := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      cases t with
      | nil => cases a <;> rfl
      | cons b u =>
          by_cases hab : a = false ∧ b = false
          · obtain ⟨rfl, rfl⟩ := hab; rw [firstDDidx_ff] at hn; simp at hn
          · have hmap : firstDDidx (a :: b :: u) = (firstDDidx (b :: u)).map (· + 1) := by
              cases a with
              | true => rw [firstDDidx_true]
              | false => cases b with
                | false => exact absurd ⟨rfl, rfl⟩ hab
                | true => rw [firstDDidx_ft]
            rw [hmap] at hn
            have hbu : firstDDidx (b :: u) = none := by
              cases hh : firstDDidx (b :: u) with
              | none => rfl
              | some j => rw [hh] at hn; simp at hn
            have hih := ih hbu
            rw [hasDD_cons]; simp only [List.head?_cons]
            have h1 : (a == false && some b == some false) = false := by
              by_cases ha : a = false <;> by_cases hb : b = false <;> simp_all
            rw [h1, Bool.false_or]; exact hih
end Psi
