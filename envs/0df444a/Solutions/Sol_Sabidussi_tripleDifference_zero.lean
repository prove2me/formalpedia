-- Prove2me | solution 1 for Sabidussi.tripleDifference_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:36.59159+00:00
-- url     : https://prove2.me/submissions/8b29b0c0-feb5-4c9c-8618-0063dc949605

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (t : Color) : tripleDifference t 0 = t := rfl
end Sabidussi
