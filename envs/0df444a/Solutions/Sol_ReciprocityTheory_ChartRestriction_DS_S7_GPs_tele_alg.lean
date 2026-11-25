-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.tele_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:20.363662+00:00
-- url     : https://prove2.me/submissions/cff6d332-82a8-418b-837c-087a2551c851

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA

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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (T : Fin n → Fin n → Fin n → Fin n → E)
    (a b : Fin n) :
    ∑ e, ∑ c', ∑ d', (P a c' * Q d' e) • ∑ c, ∑ d, (P e c * Q d b) • T c' d' c d =
      ∑ c, ∑ d, (P a c * Q d b) • ∑ e, T c e e d := by
  have hq : ∀ d' c, ∑ e, Q d' e * P e c = if d' = c then 1 else 0 := by
    intro d' c
    have h := congrFun (congrFun hQP d') c
    rwa [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [Finset.smul_sum, smul_smul]
  calc ∑ e, ∑ c', ∑ d', ∑ c, ∑ d, (P a c' * Q d' e * (P e c * Q d b)) • T c' d' c d
      = ∑ c', ∑ d', ∑ c, ∑ d, ∑ e, (P a c' * Q d' e * (P e c * Q d b)) • T c' d' c d := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ c', ∑ d', ∑ c, if d' = c then ∑ d, (P a c' * Q d b) • T c' d' c d else 0 := by
        refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d' _ =>
          Finset.sum_congr rfl fun c _ => ?_
        have key : ∀ d, ∑ e, (P a c' * Q d' e * (P e c * Q d b)) • T c' d' c d =
            (if d' = c then P a c' * Q d b else 0) • T c' d' c d := by
          intro d
          rw [← Finset.sum_smul]
          congr 1
          calc ∑ e, P a c' * Q d' e * (P e c * Q d b) = (P a c' * Q d b) * ∑ e, Q d' e * P e c := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
            _ = _ := by rw [hq]; split_ifs <;> simp
        simp only [key]
        split_ifs <;> simp
    _ = ∑ c', ∑ d', ∑ d, (P a c' * Q d b) • T c' d' d' d := by
        refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d' _ => ?_
        rw [Finset.sum_ite_eq]; simp
    _ = ∑ c, ∑ d, ∑ e, (P a c * Q d b) • T c e e d := by
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.sum_comm]
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
