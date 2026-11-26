-- Prove2me | solution 1 for Sabidussi.localDifference_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:52.922226+00:00
-- url     : https://prove2.me/submissions/f9875b96-785b-4506-90f1-89462a576931

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (c : Fin 3) :
    localDifference 0 c = doubleDifference (choiceColor c) := rfl
end Sabidussi
