-- Prove2me | solution 1 for Sabidussi.tripleDifference_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:47.005062+00:00
-- url     : https://prove2.me/submissions/ec7feb09-0202-4a83-b300-03fa49bd9ae1

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (t : Color) :
    tripleDifference t 2 = (t.1 + t.2, t.1) := rfl
end Sabidussi
