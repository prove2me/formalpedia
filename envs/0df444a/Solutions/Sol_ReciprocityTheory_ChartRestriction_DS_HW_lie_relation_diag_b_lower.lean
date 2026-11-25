-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lie_relation_diag_b_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:18.374112+00:00
-- url     : https://prove2.me/submissions/652bb1de-7854-48d8-807c-ac08defc4c5c

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
    F b b (F b a y) = F b a (F b b y) + F b a y := by
  have h := hF b b b a rfl he.symm
  rw [if_pos rfl, if_neg hab, sub_zero] at h
  have h2 := congrArg (fun T : Module.End ℂ M => T y) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
  rw [sub_eq_iff_eq_add] at h2
  rw [h2]
  abel
end ReciprocityTheory.ChartRestriction.DS.HW
