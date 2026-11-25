-- Prove2me | solution 1 for SZ.Slice.mem_MahlerZ_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:06.419141+00:00
-- url     : https://prove2.me/submissions/063eb066-35c6-4398-b2bf-707b881f6c8d

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_dvd_floor_of_uniform
import Theorems.Thm_SZ_Slice_mem_MahlerZ_of_dvd


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (S : Slice) (hp : S.p = 2) (he : S.e = (S.m : ℤ) - 1)
    (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ} (hj : 1 ≤ j) (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    Real.sqrt S.m ∈ MahlerZ :=
  mem_MahlerZ_of_dvd S hp (dvd_floor_of_uniform S he hpsq hj hk h0 h1)
end SZ.Slice
