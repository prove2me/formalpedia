-- Prove2me | solution 1 for Psi.cV_true_false_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:09:06.745856+00:00
-- url     : https://prove2.me/submissions/fc41bf70-5b41-4efd-8ea3-c45acedb2c8f

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (hp : p.head? = some true) :
    countValleys p true = countValleys p false + 1 := by
  cases p with
  | nil => simp at hp
  | cons a t => cases a with
      | true => simp [countValleys]; omega
      | false => simp at hp
end Psi
