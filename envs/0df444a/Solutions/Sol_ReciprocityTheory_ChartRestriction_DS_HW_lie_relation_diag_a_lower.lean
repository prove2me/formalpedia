-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lie_relation_diag_a_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:11:38.551111+00:00
-- url     : https://prove2.me/submissions/bc41f6e8-da00-4e11-aa05-c8def6b42a36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (hF : Formalism.REAL.KRel ε F) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b) (y : M) :
    F a a (F b a y) = F b a (F a a y) - F b a y := by
  have h := hF a a b a rfl he.symm
  rw [if_neg hab, if_pos rfl, zero_sub] at h
  have h2 := congrArg (fun T : Module.End ℂ M => T y) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply] at h2
  rw [sub_eq_iff_eq_add] at h2
  rw [h2]
  abel
end ReciprocityTheory.ChartRestriction.DS.HW
