-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.khw_real_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:47:03.911777+00:00
-- url     : https://prove2.me/submissions/55a88591-abcd-4aee-935d-f15b60e814c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dot_rhoC_rhoHol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_nsq_rho_split

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
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (δ : Fin n → ℝ) :
    nsq (δ + rhoHol ε + rhoC ε) - nsq (rhoC ε) - 2 * dot (rhoHol ε) (δ + rhoHol ε) =
      nsq (δ + rhoC ε) - nsq (rho n) := by
  rw [nsq_rho_split ε]
  have h0 := dot_rhoC_rhoHol ε
  have : nsq (δ + rhoHol ε + rhoC ε) - nsq (rhoC ε) - 2 * dot (rhoHol ε) (δ + rhoHol ε) -
      (nsq (δ + rhoC ε) - (nsq (rhoC ε) + nsq (rhoHol ε))) = 2 * dot (rhoC ε) (rhoHol ε) := by
    unfold nsq dot
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply]; ring
  rw [h0] at this
  linarith
end ReciprocityTheory.ChartRestriction.DS
