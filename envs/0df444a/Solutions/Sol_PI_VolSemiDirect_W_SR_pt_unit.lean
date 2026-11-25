-- Prove2me | solution 1 for PI.VolSemiDirect.W.SR.pt_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:29.593112+00:00
-- url     : https://prove2.me/submissions/c8b9d6b2-3a30-4208-84e2-d7fdbae2bb74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HasStableRangeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.SR
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped RestrictedProduct
namespace PI.VolSemiDirect.W.SR
theorem _root_.solution {K : Type} [Field K] (B : ValuationSubring K) {a b x y : K}
    (h : a * x + b * y = 1) (ha : a ∈ B) (hb : b ∈ B) (hx : x ∈ B) (hy : y ∈ B) :
    ∃ hm : a + (if B.valuation b ≤ B.valuation a then 0 else 1) * b ∈ B,
      IsUnit (⟨_, hm⟩ : B) := by
  have hv1 : ∀ z ∈ B, B.valuation z ≤ 1 := fun z hz => (B.valuation_le_one_iff z).2 hz
  have hone : 1 ≤ max (B.valuation a) (B.valuation b) := by
    have := Valuation.map_add B.valuation (a * x) (b * y)
    rw [h, map_one] at this
    refine this.trans (max_le_max ?_ ?_)
    · rw [map_mul]
      exact mul_le_of_le_one_right' (hv1 x hx)
    · rw [map_mul]
      exact mul_le_of_le_one_right' (hv1 y hy)
  split_ifs with hv
  · refine ⟨by rw [zero_mul, add_zero]; exact ha, (B.valuation_eq_one_iff _).2 ?_⟩
    show B.valuation (a + 0 * b) = 1
    rw [zero_mul, add_zero]
    exact le_antisymm (hv1 a ha) (by rwa [max_eq_left hv] at hone)
  · have hlt : B.valuation a < B.valuation b := not_le.1 hv
    refine ⟨by rw [one_mul]; exact add_mem ha hb, (B.valuation_eq_one_iff _).2 ?_⟩
    show B.valuation (a + 1 * b) = 1
    rw [one_mul, Valuation.map_add_eq_of_lt_right _ hlt]
    exact le_antisymm (hv1 b hb) (by rwa [max_eq_right hlt.le] at hone)
end PI.VolSemiDirect.W.SR
