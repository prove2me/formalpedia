-- Prove2me | solution 1 for SZ.Slice.mem_MahlerZ_of_e_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:58.298962+00:00
-- url     : https://prove2.me/submissions/5d5841b9-15d6-4e88-acde-54d0f1fc1ef4

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_dvd_floor_of_e_le
import Theorems.Thm_SZ_Slice_mem_MahlerZ_of_dvd

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution (S : Slice) (hp : S.p = 2) (he : S.e ≤ (S.m : ℤ) - 2) {j k₀ : ℤ}
    (hj : 1 ≤ j) (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    Real.sqrt S.m ∈ MahlerZ :=
  mem_MahlerZ_of_dvd S hp (dvd_floor_of_e_le S he hj h0 h1)
end SZ.Slice
