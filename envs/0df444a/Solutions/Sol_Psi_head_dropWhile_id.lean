-- Prove2me | solution 1 for Psi.head_dropWhile_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:42:51.41204+00:00
-- url     : https://prove2.me/submissions/7a37fadb-fa99-4e0e-b59a-e9e22678f2c9

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l : List Bool) : (l.dropWhile id).head? ≠ some true := by
  induction l with
  | nil => simp
  | cons a t ih => cases a with | true => simpa using ih | false => simp
end Psi
