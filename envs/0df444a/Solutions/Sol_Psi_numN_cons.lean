-- Prove2me | solution 1 for Psi.numN_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:29:13.281517+00:00
-- url     : https://prove2.me/submissions/f6d4f631-6257-4f5d-89a4-9544d56c4575

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : Bool) (t : List Bool) :
    numN (a :: t) = (if a = true then 1 else 0) + numN t := by
  cases a with
  | false => simp [numN]
  | true => simp [numN]; omega
end Psi
