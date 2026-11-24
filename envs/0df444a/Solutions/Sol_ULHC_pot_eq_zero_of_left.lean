-- Prove2me | solution 1 for ULHC.pot_eq_zero_of_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:31.93201+00:00
-- url     : https://prove2.me/submissions/e6eda767-0741-4412-a76b-0dfd2f0da8a0

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential

set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}
namespace ULHC
theorem _root_.solution {B : ℤ} (hB : ∀ e ∈ E, B < e.p.1) (c : Pt) (hc : c.1 ≤ B) :
    pot E w c = 0 := by
  unfold pot
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro e he hsel
  have := hB e he
  have := hsel.2.2
  omega
end ULHC
