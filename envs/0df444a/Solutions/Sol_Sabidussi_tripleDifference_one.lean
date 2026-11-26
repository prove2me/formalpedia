-- Prove2me | solution 1 for Sabidussi.tripleDifference_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:37.070054+00:00
-- url     : https://prove2.me/submissions/00e15abf-869a-487a-b375-8d89e20a4ced

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (t : Color) :
    tripleDifference t 1 = (t.2, t.1 + t.2) := rfl
end Sabidussi
