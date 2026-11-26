-- Prove2me | solution 1 for P2M_O3_pairing_neg_right__d98ee631228f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:53.72226+00:00
-- url     : https://prove2.me/submissions/7ed49963-aa00-4549-970f-c1fa471cc39b

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d : ℕ} (x y : Vec d) :
    pairing x (-y) = -pairing x y := by
  exact pairing_neg_right x y
end O3
