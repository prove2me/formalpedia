-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.exp2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:24:41.467134+00:00
-- url     : https://prove2.me/submissions/23f10427-f0ee-4af7-b768-bce520cb7403

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB

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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
local notation "𝕄f" => Fin n → Fin n → ℂ
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    A * Matrix.single (Fin.rev b) (Fin.rev a) 1 * B = ∑ c, ∑ d, ((B.submatrix Fin.revPerm Fin.revPerm) a c *
      (A.submatrix Fin.revPerm Fin.revPerm) d b) • Matrix.single (Fin.rev d) (Fin.rev c) (1 : ℂ) := by
  ext i j
  have lhs : (A * Matrix.single (Fin.rev b) (Fin.rev a) 1 * B : Matrix (Fin n) (Fin n) ℂ) i j = A i (Fin.rev b) * B (Fin.rev a) j := by
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
  rw [lhs, Matrix.sum_apply]
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Fin.rev_eq_iff, mul_comm]
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
