-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.nsq_rho_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:40.71089+00:00
-- url     : https://prove2.me/submissions/2f0bd047-b50b-41ca-b45a-be4a78755e76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carUPos_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carUPos_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rhoC_add_rhoHol_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carU_nsq_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dot_rhoC_rhoHol

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
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) : nsq (rho n) = nsq (rhoC ε) + nsq (rhoHol ε) := by
  let σ : Fin n → Fin n := fun a => ⟨carUPos ε a, carUPos_lt ε a⟩
  have hinj : Function.Injective σ := fun a a' h => carUPos_injective ε (congrArg Fin.val h)
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  have hval : ∀ a, (rhoC ε + rhoHol ε) a = rho n (σ a) := fun a => rhoC_add_rhoHol_eq ε a
  have hs : nsq (rhoC ε + rhoHol ε) = nsq (rho n) := by
    unfold nsq dot
    simp only [hval]
    exact (Equiv.ofBijective σ hbij).sum_comp (fun b => rho n b * rho n b)
  rw [← hs, carU_nsq_add, dot_rhoC_rhoHol]; ring
end ReciprocityTheory.ChartRestriction.DS
