-- Prove2me | solution 1 for Sabidussi.bracketRightHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:46.453379+00:00
-- url     : https://prove2.me/submissions/2ab2925a-22ce-473c-a9cd-7dd6aa959922

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (x y : Color) : bracketRightHom x y = bracket x y := rfl
end Sabidussi
