-- Prove2me | solution 1 for Psi.numNBeforeDD_base_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:47:34.195966+00:00
-- url     : https://prove2.me/submissions/a63db406-7a44-41cf-9b13-e77e07ace5ea

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_numNBeforeDD_append
import Theorems.Thm_Psi_hasDD_fUD
import Theorems.Thm_Psi_hasDD_replicate_true
import Theorems.Thm_Psi_numN_fUD
import Theorems.Thm_Psi_numN_replicate_true


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) :
    numNBeforeDD ((List.replicate a [true, false]).flatten
        ++ List.replicate (b + 1) true ++ List.replicate (b + 1) false)
      = a + b + 1 := by
  rw [show (List.replicate a [true, false]).flatten = fUD a from rfl, List.append_assoc]
  have hb1 : ((List.replicate (b+1) true ++ List.replicate (b+1) false)).head? = some true := by
    rw [List.replicate_succ]; simp
  have hbnd : ¬ ((fUD a).getLast? = some false ∧
      (List.replicate (b+1) true ++ List.replicate (b+1) false).head? = some false) := by
    rintro ⟨_, h2⟩; rw [hb1] at h2; simp at h2
  rw [numNBeforeDD_append _ _ (hasDD_fUD a) hbnd, numN_fUD]
  have hgl : (List.replicate (b+1) true).getLast? = some true := by
    rw [List.getLast?_replicate]; simp
  have hbnd2 : ¬ ((List.replicate (b+1) true).getLast? = some false ∧
      (List.replicate (b+1) false).head? = some false) := by
    rintro ⟨h1, _⟩; rw [hgl] at h1; simp at h1
  rw [numNBeforeDD_append _ _ (hasDD_replicate_true (b+1)) hbnd2, numN_replicate_true]
  have hfalse : numNBeforeDD (List.replicate (b+1) false) = 0 := by
    cases b with
    | zero => simp [numNBeforeDD]
    | succ k => rw [List.replicate_succ, List.replicate_succ]; rfl
  rw [hfalse]; omega
end Psi
