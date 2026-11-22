-- Prove2me | solution 1 for SZ.threeAddSqrtTen_mem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:04.7348+00:00
-- url     : https://prove2.me/submissions/8463889b-0e68-4a4e-881b-98d523c0aa33

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
import Theorems.Thm_SZ_sqrtTen_pair
import Theorems.Thm_SZ_sqrtTen_conj_neg
import Theorems.Thm_SZ_mem_MahlerZ_of_neg


set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution : (3 + Real.sqrt 10) ∈ MahlerZ :=
  mem_MahlerZ_of_neg sqrtTen_pair sqrtTen_conj_neg ⟨3, by ring⟩
    (by rintro ⟨k, hk⟩; omega)
end SZ
