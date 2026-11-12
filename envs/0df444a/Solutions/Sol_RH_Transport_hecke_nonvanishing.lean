-- Prove2me | solution 1 for RH.Transport.hecke_nonvanishing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @0xbf
-- created : 2026-11-11T16:34:32.39992+00:00
-- url     : https://prove2.me/submissions/1ba8f3d1-ac8b-45cc-9ed9-b9690a9e1c03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B015
import Theorems.Thm_RH_Transport_improved_hecke_boundary
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_one_le_re

open OAI.SevenEighths

/-- The refined family nonvanishing follows from the improved supremum boundary. -/
theorem solution
    (χ : HeckeFamily.Character) (s : ℂ)
    (hs : (4374785349 / 5000000000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 := by
  by_contra hnonzero
  have hz : HeckeFamily.LFunction χ s = 0 := hnonzero
  have hBpos : (0 : ℝ) < (4374785349 / 5000000000 : ℝ) := by norm_num
  have hspos : 0 < s.re := lt_trans hBpos hs
  have hzero : s.re ∈ HeckeZeroSupremum.zeroRealParts :=
    ⟨χ, s, hspos, hpole, hz, rfl⟩
  have hmem : s.re ∈ HeckeZeroSupremum.zeroSetWithSentinel := by
    change s.re ∈ insert (1 / 2) HeckeZeroSupremum.zeroRealParts
    exact Set.mem_insert_of_mem _ hzero
  have hbdd : BddAbove HeckeZeroSupremum.zeroSetWithSentinel := by
    refine ⟨1, ?_⟩
    intro x hx
    change x ∈ insert (1 / 2) HeckeZeroSupremum.zeroRealParts at hx
    rcases Set.mem_insert_iff.mp hx with hhalf | hzero'
    · rw [hhalf]
      norm_num
    · rcases hzero' with ⟨χ', s', hpos', hpole', hz', rfl⟩
      by_contra hle
      have hgt : 1 < s'.re := lt_of_not_ge hle
      have hnonzero' := HeckeFamily.LFunction_ne_zero_of_one_le_re χ'
        (le_of_lt hgt) hpole'
      exact hnonzero' hz'
  have hsSup : s.re ≤ sSup HeckeZeroSupremum.zeroSetWithSentinel :=
    le_csSup hbdd hmem
  have hsBound : s.re ≤ (4374785349 / 5000000000 : ℝ) := by
    calc
      s.re ≤ HeckeZeroSupremum.beta := by
        simpa [HeckeZeroSupremum.beta] using hsSup
      _ ≤ (4374785349 / 5000000000 : ℝ) :=
        RH.Transport.improved_hecke_boundary
  exact (not_lt_of_ge hsBound) hs
