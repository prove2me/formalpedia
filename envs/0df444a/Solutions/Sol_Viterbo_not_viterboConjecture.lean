-- Prove2me | solution 1 for Viterbo.not_viterboConjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:06:42.173857+00:00
-- url     : https://prove2.me/submissions/efe087cc-d704-4e6f-ad5e-2447ee6f4e76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_exists_isConvexDomain_one_lt_systolicRatio
import Theorems.Thm_Viterbo_exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ

namespace Viterbo.NotViterbo

open MeasureTheory
open scoped ENNReal

theorem vol_pos_fin {n : ℕ} {A : Set (OAI.SymmetricPolar.Phase n)} (hA : Viterbo.IsConvexDomain A) :
    0 < volume A ∧ volume A < ⊤ := by
  obtain ⟨hb, -, hi⟩ := hA
  refine ⟨?_, hb.measure_lt_top⟩
  have : 0 < volume (interior A) := isOpen_interior.measure_pos _ hi
  exact lt_of_lt_of_le this (measure_mono interior_subset)

end Viterbo.NotViterbo

open MeasureTheory
open scoped ENNReal
open Viterbo.NotViterbo in
theorem solution (n : ℕ) (hn : 2 ≤ n) : ¬ Viterbo.ViterboConjecture n := by
  intro hV
  obtain ⟨A, hA, hfin, hsys⟩ := Viterbo.exists_isConvexDomain_one_lt_systolicRatio n hn
  obtain ⟨⟨c, hc, hcA⟩, -⟩ :=
    Viterbo.exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ n (by omega)
  have h1 := hV c hc A hA
  rw [hcA A hA] at h1
  obtain ⟨hp, hf⟩ := vol_pos_fin hA
  have hd0 : (n.factorial : ℝ≥0∞) * volume A ≠ 0 := by
    refine mul_ne_zero ?_ hp.ne'
    exact_mod_cast n.factorial_ne_zero
  have hdt : (n.factorial : ℝ≥0∞) * volume A ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hf.ne
  unfold Viterbo.systolicRatio at hsys
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hd0) (Or.inl hdt), one_mul] at hsys
  exact absurd h1 (not_le.mpr hsys)

