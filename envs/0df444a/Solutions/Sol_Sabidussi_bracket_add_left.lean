-- Prove2me | solution 1 for Sabidussi.bracket_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:31.971539+00:00
-- url     : https://prove2.me/submissions/7e1dd655-526d-4132-9d79-92e0db9aa792

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (x y z : Color) :
    bracket (x + y) z = bracket x z + bracket y z := by
  simp only [bracket, Prod.fst_add, Prod.snd_add]
  ring
end Sabidussi
