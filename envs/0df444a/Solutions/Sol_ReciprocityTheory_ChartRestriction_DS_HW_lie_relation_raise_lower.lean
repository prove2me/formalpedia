-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lie_relation_raise_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:43.688383+00:00
-- url     : https://prove2.me/submissions/f7dd2806-4689-4d28-89de-9c707ae1ff57

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
theorem _root_.solution (hF : Formalism.REAL.KRel ε F) {a b : Fin n} (he : ε a = ε b) (y : M) :
    F a b (F b a y) = F b a (F a b y) + F a a y - F b b y := by
  have h := hF a b b a he he.symm
  rw [if_pos rfl, if_pos rfl] at h
  have h2 := congrArg (fun T : Module.End ℂ M => T y) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
  rw [sub_eq_iff_eq_add] at h2
  rw [h2]
  abel
end ReciprocityTheory.ChartRestriction.DS.HW
