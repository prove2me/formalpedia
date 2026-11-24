-- Prove2me | solution 1 for Psi.cc_fUD_cons_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:12:27.421572+00:00
-- url     : https://prove2.me/submissions/b1a79343-b669-440f-a5ed-2981aeda20fa

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
import Theorems.Thm_Psi_fUD_succ


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : ℕ) (q : List Bool) :
    cc (fUD a ++ true :: q) = List.replicate (a + 1) true ++ cc q := by
  induction a with
  | zero => simp [fUD, cc]
  | succ m ih =>
    rw [fUD_succ, List.append_assoc, List.cons_append]
    show true :: cc (false :: (fUD m ++ true :: q)) = List.replicate (m + 1 + 1) true ++ cc q
    have hcc : cc (false :: (fUD m ++ true :: q)) = cc (fUD m ++ true :: q) := by
      cases m with
      | zero => simp [fUD, cc]
      | succ p => rw [fUD_succ]; rfl
    rw [hcc, ih]
    conv_rhs => rw [List.replicate_succ, List.cons_append]
end Psi
