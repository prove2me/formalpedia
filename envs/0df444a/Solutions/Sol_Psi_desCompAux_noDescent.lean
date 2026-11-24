-- Prove2me | solution 1 for Psi.desCompAux_noDescent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:32:52.59256+00:00
-- url     : https://prove2.me/submissions/b5fc996a-523a-4052-b480-9ee4d0109821

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (hnd : noDescent w = true) (cur : ℕ) :
    desCompAux w cur = [cur + w.length] := by
  induction w generalizing cur with
  | nil => simp [desCompAux]
  | cons a t iht =>
    cases t with
    | nil => simp [desCompAux]
    | cons b rest =>
      simp only [noDescent] at hnd
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hnd
      have hab : (a && !b) = false := by
        rcases a with _ | _ <;> rcases b with _ | _ <;> simp_all
      simp only [desCompAux, hab, if_false, Bool.false_eq_true]
      rw [iht h2 (cur+1)]; simp [List.length_cons]; omega
end Psi
