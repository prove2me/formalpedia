-- Prove2me | solution 1 for Psi.phiPath_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:55:12.977797+00:00
-- url     : https://prove2.me/submissions/8f5ac347-8a39-4790-b507-31511f245e60

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) : phiPath w av ≠ [] := by
  fun_induction phiPath w av with
  | case1 w av h => simp [List.append_assoc, List.replicate_succ]
  | case2 w av h a after0 b w' hh av' pi rho rho' hsplit ihrec => simp
end Psi
