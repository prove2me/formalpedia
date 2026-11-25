-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_inK_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:38.470742+00:00
-- url     : https://prove2.me/submissions/2389ac5e-e37f-4143-92e5-910b247b266c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_inK_of_skew
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_single_comm

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) (c : ℂ) :
    inK ε (c • Matrix.single a b (1 : ℂ) + (-star c) • Matrix.single b a (1 : ℂ)) := by
  apply rorth_inK_of_skew
  · simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_single,
      star_one, star_star, neg_smul, Matrix.conjTranspose_neg, neg_add_rev, neg_neg]
  · rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_smul, rorth_single_comm h, rorth_single_comm h.symm]
end ReciprocityTheory.ChartRestriction.DS
