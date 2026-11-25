-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_sum_det_symm_eq_zero_0eb09c5f9247
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:16.691721+00:00
-- url     : https://prove2.me/submissions/6c337215-3a67-44d8-982f-72d9433d0d12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_det_update_eq_sum_10ad24af5154

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open MeasureTheory
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
theorem _root_.solution (A : Fin n → Fin n → ℝ) {i k : Fin n} (hik : i ≠ k)
    (S : Fin n → Fin n → ℝ) (hS : ∀ j l, S j l = S l j) :
    ∑ j, Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single j 1)) k (S j))) =
      0 := by
  simp_rw [det_update_eq_sum _ k (S _)]
  set T : Fin n → Fin n → ℝ := fun j l =>
    Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single j 1)) k
      (Pi.single l 1))) with hTdef
  have hT : ∀ j l, T j l = - T l j := by
    intro j l
    have hw : (Function.update (Function.update A i (Pi.single l 1)) k (Pi.single j 1)) =
        (Function.update (Function.update A i (Pi.single j 1)) k (Pi.single l 1)) ∘
          Equiv.swap i k := by
      funext r
      by_cases hri : r = i
      · subst hri; simp [Equiv.swap_apply_left, hik]
      · by_cases hrk : r = k
        · subst hrk; simp [Equiv.swap_apply_right, hik]
        · simp [Equiv.swap_apply_of_ne_of_ne hri hrk, hri, hrk]
    have h1 : T l j = - T j l := by
      show Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single l 1)) k
        (Pi.single j 1))) = _
      rw [hw]
      exact (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).map_swap
        (Function.update (Function.update A i (Pi.single j 1)) k (Pi.single l 1)) hik
    linarith
  have hX : ∑ j, ∑ l, S j l * T j l = - ∑ j, ∑ l, S j l * T j l := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hS l j, hT l j]; ring
  change ∑ j, ∑ l, S j l * T j l = 0
  linarith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
