-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.top_prod_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:48.73314+00:00
-- url     : https://prove2.me/submissions/f12ed310-e534-4813-9762-c9e8ae75e8eb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_UnitarySumCostOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ)
    (hf : ∀ x ∈ l, 0 ≤ f x ∧ f x ≤ c) (hc : 0 ≤ c) : (l.map f).prod ≤ c ^ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : 0 ≤ f a ∧ f a ≤ c := hf a (by simp)
    have ht : ∀ x ∈ t, 0 ≤ f x ∧ f x ≤ c := fun x hx => hf x (by simp [hx])
    have h0 : 0 ≤ (t.map f).prod := by
      apply List.prod_nonneg
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact (ht x hx).1
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul ha.2 (ih ht) h0 hc
end PI.UnitaryGroupMassFormula.UsCost
