-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKH.lowMinusUp_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:52.451354+00:00
-- url     : https://prove2.me/submissions/ff4c5d50-01c0-4a28-ab73-2990e10ad41e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TauPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LowMinusUpExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKH
variable {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKH
theorem _root_.solution {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) :
    lowMinusUp B = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
      ((if b < a then (1 : ℂ) else -1) * B a b) • Matrix.single a b (1 : ℂ) := by
  ext i j
  have hsum : (∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
      ((if b < a then (1 : ℂ) else -1) * B a b) • Matrix.single a b (1 : ℂ)) i j =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
        if a = i ∧ b = j then (if b < a then (1 : ℂ) else -1) * B a b else 0 := by
    first
    | simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
    | (simp only [Matrix.sum_apply]
       refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
       by_cases h : a = i ∧ b = j
       · rw [if_pos h]
         obtain ⟨rfl, rfl⟩ := h
         simp
       · rw [if_neg h]
         simp [Matrix.single_apply, h])
  rw [hsum]
  rw [Finset.sum_eq_single i (fun a _ ha => Finset.sum_eq_zero fun b _ => if_neg fun h => ha h.1)
    (fun h => absurd (Finset.mem_univ i) h)]
  by_cases hj : ε j = ε i ∧ j ≠ i
  · rw [Finset.sum_eq_single j (fun b _ hb => if_neg fun h => hb h.2)
      (fun h => (h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)).elim)]
    rw [if_pos ⟨rfl, rfl⟩]
    simp only [lowMinusUp, Matrix.of_apply]
    rcases lt_trichotomy j i with h | h | h
    · simp [h]
    · exact absurd h hj.2
    · simp [h, not_lt.2 h.le]
  · rw [Finset.sum_eq_zero fun b hb => if_neg fun h => hj (by
      obtain ⟨-, rfl⟩ := h
      exact (Finset.mem_filter.1 hb).2)]
    simp only [lowMinusUp, Matrix.of_apply]
    by_cases he : j = i
    · subst he
      simp
    · have hne : ε i ≠ ε j := fun h => hj ⟨h.symm, he⟩
      simp [hB i j hne]
end ReciprocityTheory.ChartRestriction.DS.S7.InfKH
