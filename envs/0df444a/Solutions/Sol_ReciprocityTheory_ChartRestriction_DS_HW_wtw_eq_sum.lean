-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.wtw_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:12.165504+00:00
-- url     : https://prove2.me/submissions/f2d18e04-b5ff-4e4b-9c23-f55f70faa3d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (w : List (Fin n × Fin n)) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → (b, a) ∈ w) ∧
      -Formalism.REAL.wordWeightShift w = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [Formalism.REAL.wordWeightShift]⟩
  | cons p w ih =>
    obtain ⟨c, hc, heq⟩ := ih
    refine ⟨fun a b => c a b + if a = p.2 ∧ b = p.1 then 1 else 0, ?_, ?_⟩
    · intro a b hab
      change c a b + (if a = p.2 ∧ b = p.1 then 1 else 0) ≠ 0 at hab
      by_cases h : c a b = 0
      · rw [h, zero_add] at hab
        split_ifs at hab with h2
        · obtain ⟨rfl, rfl⟩ := h2
          simp
        · exact absurd rfl hab
      · exact List.mem_cons_of_mem _ (hc a b h)
    · have hs : ∑ a, ∑ b, (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b = root p.2 p.1 := by
        rw [Finset.sum_eq_single p.2, Finset.sum_eq_single p.1]
        · simp
        · intro b _ hb
          simp [hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · intro a _ ha
          apply Finset.sum_eq_zero
          intro b _
          simp [ha]
        · intro h
          exact absurd (Finset.mem_univ _) h
      have e : ∀ a b, (((c a b + if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b =
          (c a b : ℝ) • root a b + (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b :=
        fun a b => by rw [Nat.cast_add, add_smul]
      simp only [e, Finset.sum_add_distrib, hs, ← heq]
      simp only [Formalism.REAL.wordWeightShift, root]
      abel
end ReciprocityTheory.ChartRestriction.DS.HW
