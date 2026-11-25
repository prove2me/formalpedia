-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.gel_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:05.824571+00:00
-- url     : https://prove2.me/submissions/ecfa2b99-557d-4dcc-b88e-20032572968a

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
theorem _root_.solution (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (S : Fin n → Fin n → E) :
    ∑ a, ∑ c, ∑ d, (P a c * Q d a) • S c d = ∑ c, S c c := by
  have hq : ∀ d c, ∑ a, Q d a * P a c = if d = c then 1 else 0 := by
    intro d c
    have h := congrFun (congrFun hQP d) c
    rwa [Matrix.mul_apply, Matrix.one_apply] at h
  calc ∑ a, ∑ c, ∑ d, (P a c * Q d a) • S c d = ∑ c, ∑ d, ∑ a, (P a c * Q d a) • S c d := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_; rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, (if d = c then S c d else 0) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_smul]
        have e : ∑ a, P a c * Q d a = if d = c then 1 else 0 := by
          rw [← hq]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
        rw [e]; split_ifs <;> simp
    _ = ∑ c, S c c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_ite_eq']; simp
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
