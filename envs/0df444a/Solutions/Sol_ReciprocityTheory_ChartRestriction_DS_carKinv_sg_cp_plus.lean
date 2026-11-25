-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carKinv_sg_cp_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:02.341613+00:00
-- url     : https://prove2.me/submissions/01b6d5ec-6830-4b35-b359-faf1b0856e6e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARKinv
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__76e6fa524bc5

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
    sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b = if b = i then cp a c else 0 := by
  have hs : sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by simp [sgE, ha, hb]
  have hcm : c ∈ minusIdx ε := by simp [minusIdx, hc]
  rw [hs, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun x _ => carKinv_triple₁ _ _ _ _ (hC i c a x).1 (hC b x i c).2.2]
  by_cases hbi : b = i
  · subst hbi
    simp [mul_ite, Finset.sum_ite_eq', hcm]
  · simp [hbi]
end ReciprocityTheory.ChartRestriction.DS
