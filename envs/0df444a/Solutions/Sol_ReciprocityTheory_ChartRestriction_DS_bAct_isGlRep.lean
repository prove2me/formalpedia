-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.bAct_isGlRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:51.8716+00:00
-- url     : https://prove2.me/submissions/505bac04-65f6-4e59-b2a6-da9d3cc7ad29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_commutator_add_sum_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_rel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_factorAd_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_comm_of_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_commutator

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
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (k : ℕ) : IsGlRep (bAct E k) := by
  intro a b c d
  simp only [bAct]
  rw [commutator_add_sum_eq _ _ _ _ (fun j => mAct_factorAd_comm k j a b c d)
    (fun i => (mAct_factorAd_comm k i c d a b).symm) (fun i j hij => factorAd_comm_of_ne k hij a b c d),
    mAct_rel hE]
  simp only [factorAd_commutator]
  by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, Finset.sum_sub_distrib] <;> abel
end ReciprocityTheory.ChartRestriction.DS
