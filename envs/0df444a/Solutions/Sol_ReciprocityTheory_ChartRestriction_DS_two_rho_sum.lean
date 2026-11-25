-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.two_rho_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:26.666465+00:00
-- url     : https://prove2.me/submissions/4255ebe1-d91b-40fe-aa6a-7aa8b3647cf4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_sum_univ_pm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_two_rhoHol_plus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_two_rhoHol_minus

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
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Module.End ℂ M) :
    (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • F a =
      ∑ a ∈ plusIdx ε, (qOf ε : ℂ) • F a - ∑ a ∈ minusIdx ε, (pOf ε : ℂ) • F a := by
  rw [Finset.smul_sum, csq_sum_univ_pm ε, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun a ha => by rw [smul_smul, csq_two_rhoHol_plus ε ha]
  · exact Finset.sum_congr rfl fun a ha => by rw [smul_smul, csq_two_rhoHol_minus ε ha, neg_smul]
end ReciprocityTheory.ChartRestriction.DS
