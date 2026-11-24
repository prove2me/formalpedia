-- Prove2me | solution 1 for PI.WFJM.Shape.pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:41.961804+00:00
-- url     : https://prove2.me/submissions/98cae049-56fd-4914-b7a2-b27f90d4594a

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
theorem _root_.solution (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (i : Fin n) :
    0 < f i ↔ (i : ℕ) < nP f := by
  classical
  unfold nP
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => 0 < f j) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hj.lt_or_eq with h | h
      · exact hseg j i h hi
      · rw [h]; exact hi
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hi
    by_contra hn
    have hsub : Finset.univ.filter (fun j => 0 < f j) ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hji
      push_neg at hji
      rcases hji.lt_or_eq with h | h
      · exact hn (hseg i j h hj)
      · rw [h] at hn; exact hn hj
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
end PI.WFJM.Shape
