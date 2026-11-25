-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carKinv_sg_cm_minus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:50.712822+00:00
-- url     : https://prove2.me/submissions/83634704-05ca-491a-8752-a77fcf0c679e

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
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = false) (hb : ε b = false) (hi : ε i = true) :
    sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b = if c = b then cm i a else 0 := by
  have hs : sgE ε cp cm a b = -∑ y ∈ plusIdx ε, cp y b * cm y a := by simp [sgE, ha, hb]
  have hip : i ∈ plusIdx ε := by simp [plusIdx, hi]
  have e : ∀ S T : Module.End ℂ W, (-S) * T - T * (-S) = -(S * T - T * S) := fun S T => by noncomm_ring
  rw [hs, e, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun y _ => carKinv_triple₂ _ _ _ _ (hC i c y b).2.2 (hC y a i c).2.1,
    Finset.sum_neg_distrib, neg_neg]
  by_cases hcb : c = b
  · subst hcb
    simp [ite_mul, Finset.sum_ite_eq, hip]
  · simp [hcb]
end ReciprocityTheory.ChartRestriction.DS
