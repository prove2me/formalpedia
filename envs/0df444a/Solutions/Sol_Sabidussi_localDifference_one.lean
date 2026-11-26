-- Prove2me | solution 1 for Sabidussi.localDifference_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:53.635539+00:00
-- url     : https://prove2.me/submissions/b8329f32-26c1-46fa-b045-e7ef9ed5a5cc

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (c : Fin 3) :
    localDifference 1 c = tripleDifference (choiceColor c) := rfl
end Sabidussi
