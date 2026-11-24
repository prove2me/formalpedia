-- Prove2me | solution 1 for Psi.northRuns_replicate_true_replicate_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:37:43.141468+00:00
-- url     : https://prove2.me/submissions/d2bb85e8-6ebe-4069-8cb2-e01b12492de5

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
import Theorems.Thm_Psi_northRunsAux_replicate_true

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (m n : ℕ) (hm : 0 < m) :
    northRuns (List.replicate m true ++ List.replicate n false) = [m] := by
  rw [northRuns, northRunsAux_replicate_true, Nat.zero_add]
  have htail : ∀ p : ℕ, northRunsAux (List.replicate p false) 0 = [] := by
    intro p; induction p with
    | zero => rfl
    | succ q ih =>
        rw [List.replicate_succ]
        simp only [northRunsAux, Nat.lt_irrefl, if_false, List.nil_append]
        exact ih
  cases n with
  | zero => simp only [List.replicate_zero]; simp [northRunsAux, hm]
  | succ p =>
    rw [List.replicate_succ]
    simp only [northRunsAux]
    rw [if_pos hm, htail p, List.append_nil]
end Psi
