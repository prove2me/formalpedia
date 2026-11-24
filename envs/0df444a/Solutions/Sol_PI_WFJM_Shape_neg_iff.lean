-- Prove2me | solution 1 for PI.WFJM.Shape.neg_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:53.097876+00:00
-- url     : https://prove2.me/submissions/145c6fec-35d4-449a-85aa-6e91cdcb9168

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}
namespace PI.WFJM.Shape
theorem _root_.solution (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0) (i : Fin n) :
    f i < 0 ↔ n - nN f ≤ (i : ℕ) := by
  classical
  unfold nN
  have hin := i.isLt
  constructor
  · intro hi
    have hsub : Finset.Ici i ⊆ Finset.univ.filter (fun j => f j < 0) := by
      intro j hj
      rw [Finset.mem_Ici] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hj.lt_or_eq with h | h
      · exact hseg i j h hi
      · rw [← h]; exact hi
    have := Finset.card_le_card hsub
    rw [Fin.card_Ici] at this
    omega
  · intro hi
    by_contra hn
    have hsub : Finset.univ.filter (fun j => f j < 0) ⊆ Finset.Ioi i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Ioi]
      by_contra hji
      push_neg at hji
      rcases hji.lt_or_eq with h | h
      · exact hn (hseg j i h hj)
      · rw [← h] at hn; exact hn hj
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    omega
end PI.WFJM.Shape
