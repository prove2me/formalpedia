-- Prove2me | solution 1 for UniformCounting.uniformProbability_and
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T15:18:56.256255+00:00
-- url     : https://prove2.me/submissions/80a1d63d-fca4-4e4a-90ac-a468e93ff325

import Mathlib
import Definitions.Def_OnlineStochMatching_SuggestedMatching_BallsInBins

set_option autoImplicit false

-- carved from submission 4a5e26af-423d-4e99-b667-4dcd719297c2, lines 1144-1168

theorem solution {Ω : Type} [Fintype Ω] (P Q : Ω → Prop) :
    OnlineStochMatching.SuggestedMatching.uniformProbability P +
        OnlineStochMatching.SuggestedMatching.uniformProbability Q - 1 ≤
      OnlineStochMatching.SuggestedMatching.uniformProbability (fun ω => P ω ∧ Q ω) := by
  classical
  unfold OnlineStochMatching.SuggestedMatching.uniformProbability
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · simp [h0]
  · have hC : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hpos
    have h1 := Finset.card_union_add_card_inter (Finset.univ.filter P) (Finset.univ.filter Q)
    have h2 : (Finset.univ.filter P ∪ Finset.univ.filter Q).card ≤ Fintype.card Ω := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    have h3 : Finset.univ.filter P ∩ Finset.univ.filter Q =
        @Finset.filter _ (fun ω => P ω ∧ Q ω) (fun ω => Classical.propDecidable _) Finset.univ := by
      ext ω; simp
    rw [h3] at h1
    have h4 : ((Finset.univ.filter P).card : ℝ) + (Finset.univ.filter Q).card
        ≤ Fintype.card Ω +
          (@Finset.filter _ (fun ω => P ω ∧ Q ω) (fun ω => Classical.propDecidable _) Finset.univ).card := by
      exact_mod_cast (by omega : (Finset.univ.filter P).card + (Finset.univ.filter Q).card ≤ _)
    have e : ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω +
        (Finset.univ.filter Q).card / Fintype.card Ω - 1
        = ((Finset.univ.filter P).card + (Finset.univ.filter Q).card
          - Fintype.card Ω) / Fintype.card Ω := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hC.le
