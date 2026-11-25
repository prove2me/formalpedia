-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carKinv_sg_cm_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:54.789273+00:00
-- url     : https://prove2.me/submissions/3a34f725-e107-4b14-a7c4-860aeacf2ac2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARKinv
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__e3195b73385c

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
theorem _root_.solution {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = true) (hb : ε b = true) (hc : ε c = false) :
    sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b = -(if i = a then cm b c else 0) := by
  have hs : sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by simp [sgE, ha, hb]
  have hcm : c ∈ minusIdx ε := by simp [minusIdx, hc]
  rw [hs, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun x _ => carKinv_triple₂ _ _ _ _ (hC i c a x).2.2 (hC b x i c).2.1,
    Finset.sum_neg_distrib]
  congr 1
  by_cases hia : i = a
  · subst hia
    simp [ite_mul, Finset.sum_ite_eq, hcm]
  · simp [hia]
end ReciprocityTheory.ChartRestriction.DS
