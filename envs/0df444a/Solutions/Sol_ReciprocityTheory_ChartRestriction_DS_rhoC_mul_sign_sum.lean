-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rhoC_mul_sign_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:12.786985+00:00
-- url     : https://prove2.me/submissions/d427c8b8-0bc1-4840-bbcb-809750be0a67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (g : Bool → ℝ) :
    ∑ a, rhoC ε a * g (ε a) = 0 := by
  have hT : ∑ a : Fin n, ∑ b : Fin n, (if a < b ∧ ε b = ε a then g (ε a) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if b < a ∧ ε b = ε a then g (ε a) else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    by_cases h : b < a ∧ ε a = ε b
    · rw [if_pos h, if_pos ⟨h.1, h.2.symm⟩, h.2]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.symm⟩)]
  have e : ∀ a, rhoC ε a * g (ε a) = (∑ b, (if a < b ∧ ε b = ε a then g (ε a) else 0) -
      ∑ b, (if b < a ∧ ε b = ε a then g (ε a) else 0)) / 2 := by
    intro a
    unfold rhoC
    rw [natCast_card_filter, natCast_card_filter]
    have e1 : ∑ b, (if a < b ∧ ε b = ε a then g (ε a) else 0) =
        g (ε a) * ∑ b, (if a < b ∧ ε b = ε a then (1:ℝ) else 0) := by
      rw [mul_sum]; simp [mul_ite]
    have e2 : ∑ b, (if b < a ∧ ε b = ε a then g (ε a) else 0) =
        g (ε a) * ∑ b, (if b < a ∧ ε b = ε a then (1:ℝ) else 0) := by
      rw [mul_sum]; simp [mul_ite]
    rw [e1, e2]; ring
  simp only [e]
  rw [← sum_div, sum_sub_distrib, hT, sub_self, zero_div]
end ReciprocityTheory.ChartRestriction.DS
