-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tset_casVal_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:03.207574+00:00
-- url     : https://prove2.me/submissions/64357f9e-5d7a-4db7-a9ad-4803627c2739

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (lam : Fin n → ℝ) (s : Fin n) :
    casVal (lam + Pi.single s 1) = casVal lam + 2 * lam s + 1 := by
  have key : ∀ a, (lam + Pi.single s (1 : ℝ) : Fin n → ℝ) a * (lam + Pi.single s (1 : ℝ) : Fin n → ℝ) a =
      lam a * lam a + (if a = s then 2 * lam s + 1 else 0) := by
    intro a
    by_cases h : a = s
    · subst h; rw [Pi.add_apply, Pi.single_eq_same, if_pos rfl]; ring
    · rw [Pi.add_apply, Pi.single_eq_of_ne h, if_neg h]; ring
  simp only [casVal, nsq, dot, key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp <;> ring
end ReciprocityTheory.ChartRestriction.DS
