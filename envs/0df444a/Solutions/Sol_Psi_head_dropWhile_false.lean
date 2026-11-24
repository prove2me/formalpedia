-- Prove2me | solution 1 for Psi.head_dropWhile_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:43:12.448187+00:00
-- url     : https://prove2.me/submissions/0aaa4fbd-50fa-4b07-a12b-26683618c157

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l : List Bool) : (l.dropWhile (· = false)).head? ≠ some false := by
  induction l with
  | nil => simp
  | cons a t ih => cases a with | false => simpa using ih | true => simp
end Psi
