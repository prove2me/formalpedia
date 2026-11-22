-- Prove2me | solution 1 for SZ.eventually_composite_sqrtTen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:06.677682+00:00
-- url     : https://prove2.me/submissions/b1ecfc5f-aec6-4b93-b742-059b77d43fe6

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
import Theorems.Thm_SZ_eventually_composite
import Theorems.Thm_SZ_sqrtTen_pair
import Theorems.Thm_SZ_sqrtTen_conj_neg

set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution :
    ∀ᶠ n in atTop,
      ¬ Prime ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ ∧
      1 < ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ :=
  eventually_composite (m := 6) sqrtTen_pair sqrtTen_conj_neg (by norm_num) ⟨1, by ring⟩
    ⟨0, by ring⟩
end SZ
