-- Prove2me | solution 1 for SZ.six_dvd_floor_sqrtTen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:00.27652+00:00
-- url     : https://prove2.me/submissions/97a75526-dd41-4deb-afdd-049be434a188

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
    (6 : ℤ) ∣ ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ :=
  dvd_floor_of_neg sqrtTen_pair sqrtTen_conj_neg ⟨1, by ring⟩ ⟨0, by ring⟩ n
end SZ
