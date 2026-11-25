-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.glRep_rsM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:32.519381+00:00
-- url     : https://prove2.me/submissions/c238dcc0-4f26-4dcb-9e6d-111eef5ddc30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rsM_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rsM_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rsM_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rsM_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS
private lemma ss_lemma {n : ℕ} (a b c d : Fin n) :
    single a b (1 : ℂ) * single c d 1 = if b = c then single a d 1 else 0 := by
  split_ifs with h
  · subst h
    simp [Matrix.single_mul_single_same]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    split_ifs with h1 h2 <;> simp_all
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (n : ℕ) : IsGlRep (fun a b : Fin n => rsM (single a b (1 : ℂ))) := by

  intro a b c d
  simp only
  rw [rsM_mul, rsM_mul, rsM_sub, ss_lemma, ss_lemma]
  split_ifs <;> simp only [sub_zero, zero_sub, sub_self, rsM_zero, rsM_neg, rsM_sub]
end ReciprocityTheory.ChartRestriction.DS
