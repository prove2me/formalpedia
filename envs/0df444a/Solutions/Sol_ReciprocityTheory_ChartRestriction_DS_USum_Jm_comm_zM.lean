-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.Jm_comm_zM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:15.993804+00:00
-- url     : https://prove2.me/submissions/2fe0621a-2ca0-4d86-9dd9-813d826ff05f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution {a b : Fin n} (hab : ε a = ε b) (c : ℂ) : Jm ε * zM a b c = zM a b c * Jm ε := by
  have hd : ∀ i j, (i = a ∧ j = b) ∨ (i = b ∧ j = a) →
      (if ε i then (1 : ℂ) else -1) = if ε j then 1 else -1 := by
    rintro i j (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hab]
  unfold Jm
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : (i = a ∧ j = b) ∨ (i = b ∧ j = a)
  · rw [hd i j hij, mul_comm]
  · have hz : zM a b c i j = 0 := by
      unfold zM
      simp only [Matrix.sub_apply, Matrix.single_apply]
      push_neg at hij
      rw [if_neg, if_neg, sub_zero]
      · exact fun h => hij.2 h.1.symm h.2.symm
      · exact fun h => hij.1 h.1.symm h.2.symm
    rw [hz, mul_zero, zero_mul]
end ReciprocityTheory.ChartRestriction.DS.USum
