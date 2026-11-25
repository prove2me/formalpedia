-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimirK_khwVec_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:46.473376+00:00
-- url     : https://prove2.me/submissions/fd8373b2-a847-409c-a290-1beeef0385b9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_pair_apply_khw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_hwTerm


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
theorem _root_.solution (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ W}
    (hE : ∀ a b, ε a = ε b → E a b * E b a - E b a * E a b = E a a - E b b)
    {μ : Fin n → ℝ} {v : W} (hv : IsKHWVec ε E μ v) :
    casimirK ε E v = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • v := by
  have hsum : casimirK ε E v =
      ((∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), hwTerm μ a b : ℝ) : ℂ) • v := by
    unfold casimirK
    simp only [LinearMap.sum_apply]
    push_cast
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact pair_apply_khw (hE a b hb.symm) hv.1 (fun h => hv.2 a b h hb.symm) (fun h => hv.2 b a h hb)
  rw [hsum]
  congr 3
  exact sum_hwTerm (fun a b : Fin n => ε b = ε a) (fun _ => rfl) (fun a b h => h.symm) μ (rhoC ε)
    (fun a => by unfold rhoC; ring)
end ReciprocityTheory.ChartRestriction.DS
