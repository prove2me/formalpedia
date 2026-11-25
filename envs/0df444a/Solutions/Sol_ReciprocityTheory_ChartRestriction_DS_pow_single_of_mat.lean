-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.pow_single_of_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:27.007876+00:00
-- url     : https://prove2.me/submissions/0d047079-6a0b-4614-8e9d-d9462c8539f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_AntiEIsGlRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (A : Module.End ℂ (Fin n → M)) (T : Fin n → Fin n → Module.End ℂ M)
    (hA : ∀ f s, A f s = ∑ r, T s r (f r)) (k : ℕ) (c : Fin n) (x : M) :
    (A ^ k) (Pi.single c x) = fun s => ePow T k s c x := by
  induction k with
  | zero =>
    funext s
    simp only [pow_zero, ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, Module.End.one_apply]
    by_cases h : s = c
    · subst h; simp
    · simp [h]
  | succ k ih =>
    funext s
    rw [pow_succ', Module.End.mul_apply, ih, hA]
    simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply, LinearMap.sum_apply,
      Module.End.mul_apply]
end ReciprocityTheory.ChartRestriction.DS
