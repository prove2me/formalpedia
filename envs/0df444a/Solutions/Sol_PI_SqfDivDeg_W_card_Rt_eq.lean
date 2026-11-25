-- Prove2me | solution 1 for PI.SqfDivDeg.W.card_Rt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:54.703632+00:00
-- url     : https://prove2.me/submissions/4a86df2b-ab49-4c8d-896e-3f20273c4887

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical
namespace PI.SqfDivDeg.W
theorem _root_.solution {g : ℕ} [Fact g.Prime] (n : ℕ) :
    (Rt g n).card = ∑ f ∈ Mon g n, (if (rts f).card = 0 then 0 else 1) := by
  rw [Rt, Finset.card_filter]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  have e : (∃ x, f.IsRoot x) ↔ (rts f).card ≠ 0 := by
    rw [Finset.card_ne_zero]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp only [rts, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp only [rts, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx⟩
  by_cases h : (rts f).card = 0
  · have : ¬ ∃ x, f.IsRoot x := fun hx => e.mp hx h
    rw [if_neg this, if_pos h]
  · rw [if_pos (e.mpr h), if_neg h]
end PI.SqfDivDeg.W
