-- Prove2me | solution 1 for Psi.areaH_replicate_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:10:20.378533+00:00
-- url     : https://prove2.me/submissions/7d592379-a213-46c6-a228-339da7baebd9

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) (ht : Int) (le : Bool) :
    areaH (List.replicate n true) ht le = if (le ∧ 1 ≤ n) then ht else 0 := by
  cases n with
  | zero => simp [areaH]
  | succ m =>
    rw [List.replicate_succ]; simp only [areaH]
    have h0 : ∀ (h2 : Int), areaH (List.replicate m true) h2 false = 0 := by
      intro h2; induction m generalizing h2 with
      | zero => simp [areaH]
      | succ k ih => rw [List.replicate_succ]; simp only [areaH]; rw [ih]; simp
    rw [h0]; cases le <;> simp
end Psi
