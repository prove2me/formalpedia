-- Prove2me | solution 1 for SZ.even_floor_silver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:16.6168+00:00
-- url     : https://prove2.me/submissions/3e188e15-65d2-441b-9a25-92fd226eecc2

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
import Theorems.Thm_SZ_floor_silver
import Theorems.Thm_SZ_rec2_dvd_sub


set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution (n : ℕ) :
    Even ⌊(2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ n⌋ := by
  rw [floor_silver]
  have := rec2_dvd_sub (m := 2) (A := 2) (B := 1) (t₀ := (1 : ℤ)) (t₁ := (0 : ℤ))
    ⟨1, by ring⟩ ⟨0, by ring⟩ n
  obtain ⟨k, hk⟩ := this
  exact ⟨k, by omega⟩
end SZ
