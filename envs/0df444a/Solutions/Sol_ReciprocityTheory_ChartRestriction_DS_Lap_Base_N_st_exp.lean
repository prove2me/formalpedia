-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.st_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:42.269718+00:00
-- url     : https://prove2.me/submissions/f206e483-fb65-43f3-8b1c-d54ed72ae10e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}
variable [FiniteDimensional ℝ A]
variable {st : A →ₗ[ℝ] A}
omit [FiniteDimensional ℝ A]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (hF : IsFil F L) (hst : IsAdj F st) {Y : A} (hY : Y ∈ F 0) :
    st (NormedSpace.exp Y) = NormedSpace.exp (st Y) := by
  have hpow : ∀ n : ℕ, st (Y ^ n) = (st Y) ^ n := by
    intro n
    induction n with
    | zero => simp [hst.one]
    | succ n ih => rw [pow_succ, hst.mul, ih, pow_succ']
  rw [hF.exp_eq hY, hF.exp_eq (hst.mem Y hY), map_add, map_add, map_sum, hst.one]
  simp only [map_smul, hpow]
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
