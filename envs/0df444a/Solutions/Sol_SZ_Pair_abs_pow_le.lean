-- Prove2me | solution 1 for SZ.Pair.abs_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:47:42.276022+00:00
-- url     : https://prove2.me/submissions/2b7d3d9b-5223-4b91-ba5b-8728a3e99c09

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign

set_option autoImplicit false
open SZ
open SZ.Pair
variable {α β : ℝ} {a b : ℤ}
namespace SZ.Pair
theorem _root_.solution (h : Pair α β a b) (n : ℕ) : |β ^ n| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h.absLt.le
end SZ.Pair
