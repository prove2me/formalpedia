-- Prove2me | solution 1 for RH.Transport.original_hecke_boundary
-- status  : ACCEPTED   (prove)
-- author  : @0xbf
-- created : 2026-11-11T16:46:46.379457+00:00
-- url     : https://prove2.me/submissions/f46159ca-ab33-432c-91a9-6bcd90c50d5b

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B015
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re

open OAI.SevenEighths

theorem solution : HeckeZeroSupremum.beta ≤ (7 / 8 : ℝ) := by
  have hnonempty : HeckeZeroSupremum.zeroSetWithSentinel.Nonempty := by
    refine ⟨1 / 2, ?_⟩
    change (1 / 2 : ℝ) ∈ insert (1 / 2) HeckeZeroSupremum.zeroRealParts
    exact Set.mem_insert _ _
  have hupper : ∀ x ∈ HeckeZeroSupremum.zeroSetWithSentinel, x ≤ (7 / 8 : ℝ) := by
    intro x hx
    change x ∈ insert (1 / 2) HeckeZeroSupremum.zeroRealParts at hx
    rcases Set.mem_insert_iff.mp hx with hhalf | hzero
    · rw [hhalf]
      norm_num
    · rcases hzero with ⟨χ, s, hspos, hpole, hz, rfl⟩
      by_contra hn
      have hs : (7 / 8 : ℝ) < s.re := lt_of_not_ge hn
      have hpole' : ¬ (χ.residue = 1 ∧ s = 1) := by
        rintro ⟨hres, hsone⟩
        rcases hpole with hsne | hresne
        · exact hsne hsone
        · exact hresne hres
      exact (HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole') hz
  change sSup HeckeZeroSupremum.zeroSetWithSentinel ≤ (7 / 8 : ℝ)
  exact csSup_le hnonempty hupper
