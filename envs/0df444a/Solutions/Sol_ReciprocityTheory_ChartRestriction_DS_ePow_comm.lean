-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ePow_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:31.27626+00:00
-- url     : https://prove2.me/submissions/b3279626-5775-469a-a40f-26a678063ccd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Lemmata_MiscLemmasP_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_commutator_mul_right

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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (k : ℕ) (a b c d : Fin n) :
    E a b * ePow E k c d - ePow E k c d * E a b =
      (if b = c then ePow E k a d else 0) - (if d = a then ePow E k c b else 0) := by
  have hz : ∀ c d, ePow E 0 c d = if c = d then 1 else 0 := fun c d => rfl
  have hs : ∀ k c d, ePow E (k + 1) c d = ∑ e, E c e * ePow E k e d := by
    intro k c d
    unfold ePow Bl.ThirdBlockLemmaA.goal1
    simp [pow_succ', Matrix.mul_apply]
  induction k generalizing c d with
  | zero =>
    simp only [hz]
    split_ifs <;> subst_vars <;> simp_all
  | succ k ih =>
    rw [hs, hs, hs, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [commutator_mul_right, hE a b c, ih]
    by_cases hbc : b = c <;> by_cases hda : d = a <;>
      simp [hbc, hda, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, mul_ite,
        Finset.sum_ite_eq, Finset.sum_ite_eq', mul_assoc] <;> abel
end ReciprocityTheory.ChartRestriction.DS
