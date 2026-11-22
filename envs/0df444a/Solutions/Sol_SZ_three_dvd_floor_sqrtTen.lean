-- Prove2me | solution 1 for SZ.three_dvd_floor_sqrtTen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:04.064725+00:00
-- url     : https://prove2.me/submissions/50f0435a-39fd-4623-9879-d0ec2c49c375

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
import Theorems.Thm_SZ_sqrtTen_pair
import Theorems.Thm_SZ_sqrtTen_conj_neg
import Theorems.Thm_SZ_dvd_floor_of_neg


set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution (n : ℕ) :
    (3 : ℤ) ∣ ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ :=
  dvd_floor_of_neg sqrtTen_pair sqrtTen_conj_neg ⟨2, by ring⟩ ⟨0, by ring⟩ n
end SZ
