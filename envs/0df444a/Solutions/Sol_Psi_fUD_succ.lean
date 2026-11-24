-- Prove2me | solution 1 for Psi.fUD_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:53:13.934227+00:00
-- url     : https://prove2.me/submissions/2affa99a-b249-4b40-b67a-49898ddade20

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : Nat) : fUD (a+1) = [true, false] ++ fUD a := by
  unfold fUD; rw [List.replicate_succ, List.flatten_cons]
end Psi
