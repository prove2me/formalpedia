-- Prove2me | solution 1 for ULHC.pot_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:54.657315+00:00
-- url     : https://prove2.me/submissions/1913aa11-4dd8-45fc-b538-1dae12089f12

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential

set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}
namespace ULHC
theorem _root_.solution (E : Finset Edge) (w₁ w₂ : Edge → ℤ) (c : Pt) :
    pot E (fun e => w₁ e - w₂ e) c = pot E w₁ c - pot E w₂ c := by
  unfold pot; rw [Finset.sum_sub_distrib]
end ULHC
