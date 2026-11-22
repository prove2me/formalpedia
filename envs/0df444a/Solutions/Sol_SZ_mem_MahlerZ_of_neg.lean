-- Prove2me | solution 1 for SZ.mem_MahlerZ_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:59.419082+00:00
-- url     : https://prove2.me/submissions/e470c670-d36c-4271-961f-e26d8fe5e9e3

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
import Theorems.Thm_SZ_xiDesign_pos
import Theorems.Thm_SZ_dvd_floor_of_neg

set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution (h : Pair α β a b) (hβ : β < 0) (ha : Even a) (hb : ¬ Even b) :
    α ∈ MahlerZ := by
  refine ⟨h.one_lt, xiDesign α β, ne_of_gt (xiDesign_pos h hβ), fun n _ => ?_⟩
  have hb2 : (2 : ℤ) ∣ (b - 1) := by
    rcases Int.even_or_odd b with hbe | hbo
    · exact absurd hbe hb
    · obtain ⟨k, hk⟩ := hbo; exact ⟨k, by omega⟩
  obtain ⟨k, hk⟩ := dvd_floor_of_neg h hβ ha.two_dvd hb2 n
  exact ⟨k, by omega⟩
end SZ
