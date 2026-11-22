-- Prove2me | solution 1 for SZ.dvd_floor_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:09.252252+00:00
-- url     : https://prove2.me/submissions/6bc3ed32-5bdd-4f5e-b4f2-92c2b7e1fc08

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
import Theorems.Thm_SZ_floorNeg
import Theorems.Thm_SZ_rec2_dvd_sub


set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution {m : ℤ} (h : Pair α β a b) (hβ : β < 0) (ha : m ∣ a)
    (hb : m ∣ (b - 1)) (n : ℕ) : m ∣ ⌊xiDesign α β * α ^ n⌋ := by
  rw [floorNeg h hβ n]
  exact rec2_dvd_sub (t₀ := (1 : ℤ)) (t₁ := (0 : ℤ)) ha hb n
end SZ
