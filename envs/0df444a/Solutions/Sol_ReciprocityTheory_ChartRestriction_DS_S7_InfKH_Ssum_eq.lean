-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKH.Ssum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:43.160045+00:00
-- url     : https://prove2.me/submissions/2f80e50c-4563-4937-a274-b596a33ec98d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TauPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LowMinusUpExpand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKH_lowMinusUp_expand

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
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (x A : Matrix (Fin n) (Fin n) ℂ) (k : KG ε)
    (hB : IsBlock ε (toMK k⁻¹ * A * toMK k)) :
    Ssum T μ x A k = InfKA.DkL T μ x k (lowMinusUp (toMK k⁻¹ * A * toMK k)) +
      (-4 * ∑ a, ((rhoC ε a : ℝ) : ℂ) * (toMK k⁻¹ * A * toMK k) a a) • Gint T μ x k := by
  have hφ : ∀ (a b : Fin n) (M : Matrix (Fin n) (Fin n) ℂ), InfKA.entryCLM a b M = M a b :=
    fun _ _ _ => rfl
  simp only [Ssum, InfKA.Ek, smul_add, Finset.sum_add_distrib, smul_smul, hφ]
  set A' := toMK k⁻¹ * A * toMK k with hA'
  have hl : ∀ a b, (A' * Matrix.single a b (1 : ℂ) - Matrix.single a b (1 : ℂ) * A') a b =
      A' a a - A' b b := by
    intro a b
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
  congr 1
  · rw [lowMinusUp_expand hB, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul]
  · simp only [← Finset.sum_smul]
    congr 1
    simp only [hl, Finset.sum_filter]
    have hsplit : ∀ a b : Fin n,
        (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * (A' a a - A' b b) else 0) =
          (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * A' a a else 0) +
          (if ε a = ε b ∧ a ≠ b then (if a < b then (1 : ℂ) else -1) * A' b b else 0) := by
      intro a b
      by_cases h : ε b = ε a ∧ b ≠ a
      · have h' : ε a = ε b ∧ a ≠ b := ⟨h.1.symm, Ne.symm h.2⟩
        rw [if_pos h, if_pos h, if_pos h']
        rcases lt_or_gt_of_ne h.2 with hab | hab
        · simp only [if_pos hab, if_neg (not_lt.2 hab.le)]
          ring
        · simp only [if_pos hab, if_neg (not_lt.2 hab.le)]
          ring
      · have h' : ¬ (ε a = ε b ∧ a ≠ b) := fun h' => h ⟨h'.1.symm, Ne.symm h'.2⟩
        rw [if_neg h, if_neg h, if_neg h', add_zero]
    simp only [hsplit, Finset.sum_add_distrib]
    conv_lhs => arg 2; rw [Finset.sum_comm]
    rw [← two_mul]
    have hc : ∀ a, ∑ b, (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * A' a a else 0) =
        -2 * ((rhoC ε a : ℝ) : ℂ) * A' a a := by
      intro a
      have hp : ∀ b, (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * A' a a else 0) =
          ((if b < a ∧ ε b = ε a then (1 : ℂ) else 0) - (if a < b ∧ ε b = ε a then (1 : ℂ) else 0)) *
            A' a a := by
        intro b
        rcases lt_trichotomy b a with h | rfl | h
        · by_cases he : ε b = ε a <;> simp [h, he, ne_of_lt h, not_lt.2 h.le]
        · simp
        · by_cases he : ε b = ε a <;> simp [h, he, ne_of_gt h, not_lt.2 h.le]
      simp only [hp]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
      delta rhoC
      push_cast
      ring
    simp only [hc]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
end ReciprocityTheory.ChartRestriction.DS.S7.InfKH
