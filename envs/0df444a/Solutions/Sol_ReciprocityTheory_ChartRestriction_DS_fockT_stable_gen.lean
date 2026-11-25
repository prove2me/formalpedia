-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.fockT_stable_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:17.759596+00:00
-- url     : https://prove2.me/submissions/171230e1-1ee9-405d-83de-74d882d43537

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockT_cm_cp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockT_cm_cm

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
theorem _root_.solution {E cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (hK : CommutesCAR E cp cm) (ε : Fin n → Bool) {j b : Fin n} (hjb : ¬(ε j = true ∧ ε b = false))
    {x : W} (hx : ∀ j b, ¬(ε j = true ∧ ε b = false) → cm j b x = 0) :
    (∀ a c, cm j b (E a c x) = 0) ∧ (∀ a c, cm j b (diagE ε E cp cm a c x) = 0) ∧
      cm j b (dOp ε E cp x) = 0 ∧ cm j b (dOp' ε E cm x) = 0 := by
  have hEc : ∀ a c y, cm j b (E a c y) = E a c (cm j b y) := fun a c y => by
    have h := LinearMap.congr_fun (hK a c j b).2 y
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have hx0 := hx j b hjb
  have hE0 : ∀ a c, cm j b (E a c x) = 0 := fun a c => by rw [hEc, hx0, map_zero]
  have hcpcm : ∀ u v w z, ε u = true ∧ ε v = false → cm j b (cp u v (cm w z x)) = 0 := by
    intro u v w z huv
    rw [fockT_cm_cp hC hjb huv, fockT_cm_cm hC, hx0]
    simp
  refine ⟨hE0, fun a c => ?_, ?_, ?_⟩
  · simp only [diagE, LinearMap.add_apply, map_add, hE0, zero_add, sgE]
    split_ifs with h1 h2
    · simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply]
      refine Finset.sum_eq_zero fun y hy => hcpcm _ _ _ _ ⟨h1.1, ?_⟩
      simpa [minusIdx] using hy
    · simp only [LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Module.End.mul_apply]
      refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i hi => hcpcm _ _ _ _ ⟨?_, h2.2⟩)
      simpa [plusIdx] using hi
    · simp
  · simp only [dOp, LinearMap.sum_apply, map_sum, Module.End.mul_apply]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun a ha => ?_
    rw [hEc, fockT_cm_cp hC hjb ⟨by simpa [plusIdx] using hi, by simpa [minusIdx] using ha⟩, hx0]
    simp
  · simp only [dOp', LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Module.End.mul_apply]
    refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a _ => ?_)
    rw [hEc, fockT_cm_cm hC, hx0]
    simp
end ReciprocityTheory.ChartRestriction.DS
