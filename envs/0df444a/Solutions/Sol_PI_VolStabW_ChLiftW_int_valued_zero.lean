-- Prove2me | solution 1 for PI.VolStabW.ChLiftW.int_valued_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:57:06.042974+00:00
-- url     : https://prove2.me/submissions/b90520fe-4866-4a07-9b52-075f47596404

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensChLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open PI PI.VolStabW
open PI.VolStabW.ChLiftW
namespace PI.VolStabW.ChLiftW
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] (ψ : Y → ℝ)
    (hψ : Continuous ψ) (hint : ∀ p, ∃ n : ℤ, ψ p = n) (a : Y) (ha : ψ a = 0) (p : Y) :
    ψ p = 0 := by
  obtain ⟨n, hn⟩ := hint p
  have key : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) (n : ℝ) → ∃ m : ℤ, t = m := by
    intro t ht
    rcases le_total (0 : ℝ) n with h | h
    · rw [Set.uIcc_of_le h] at ht
      obtain ⟨q, hq⟩ := intermediate_value_univ a p hψ (by rw [ha, hn]; exact ht)
      obtain ⟨m, hm⟩ := hint q
      exact ⟨m, by rw [← hq, hm]⟩
    · rw [Set.uIcc_of_ge h] at ht
      obtain ⟨q, hq⟩ := intermediate_value_univ p a hψ (by rw [ha, hn]; exact ht)
      obtain ⟨m, hm⟩ := hint q
      exact ⟨m, by rw [← hq, hm]⟩
  rw [hn]
  by_contra hne
  have hn0 : n ≠ 0 := fun h => hne (by simp [h])
  rcases lt_or_gt_of_ne hn0 with h | h
  · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    obtain ⟨m, hm⟩ := key (-1 / 2) (by
      rw [Set.uIcc_of_ge (by linarith)]
      constructor <;> linarith)
    have h2 : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
    have h3 : 2 * m = -1 := by exact_mod_cast h2
    omega
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    obtain ⟨m, hm⟩ := key (1 / 2) (by
      rw [Set.uIcc_of_le (by linarith)]
      constructor <;> linarith)
    have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega
end PI.VolStabW.ChLiftW
