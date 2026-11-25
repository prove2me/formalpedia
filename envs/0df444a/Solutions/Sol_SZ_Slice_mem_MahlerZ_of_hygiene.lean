-- Prove2me | solution 1 for SZ.Slice.mem_MahlerZ_of_hygiene
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:39.663049+00:00
-- url     : https://prove2.me/submissions/dbde9eea-670d-48ac-afcf-ec2716c3a884

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_dvd_floor_of_hygiene
import Theorems.Thm_SZ_Slice_mem_MahlerZ_of_dvd

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution (S : Slice) (hp : S.p = 2) {j k₀ : ℤ} (hj : 1 ≤ j)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U)
    (hA : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.dA (S.w0 j k₀) i ≤ (S.m : ℤ) - 2)
    (hB : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.e - S.dB (S.w0 j k₀) i ≤ (S.m : ℤ) - 2) :
    Real.sqrt S.m ∈ MahlerZ :=
  mem_MahlerZ_of_dvd S hp (dvd_floor_of_hygiene S hj h0 h1 hA hB)
end SZ.Slice
