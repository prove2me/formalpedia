-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimirK_pm
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:15:18.578806+00:00
-- url     : https://prove2.me/submissions/31f8b0b2-e529-4ad0-b51e-b21c305d474a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
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

theorem ReciprocityTheory.ChartRestriction.DS.casimirK_pm {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ M) :
    casimirK ε F = ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, F a b * F b a +
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, F a b * F b a := by
  unfold casimirK plusIdx minusIdx
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun a => ε a = true)]
  have hf : (Finset.univ.filter fun a => ¬ ε a = true) = Finset.univ.filter fun a => ε a = false := by
    ext a; simp
  rw [hf]
  congr 1
  · refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b; simp [ha]
  · refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b; simp [ha]


end

theorem solution {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ M) :
    ReciprocityTheory.ChartRestriction.DS.casimirK ε F =
      ∑ a ∈ ReciprocityTheory.ChartRestriction.DS.plusIdx ε, ∑ b ∈ ReciprocityTheory.ChartRestriction.DS.plusIdx ε, F a b * F b a +
      ∑ a ∈ ReciprocityTheory.ChartRestriction.DS.minusIdx ε, ∑ b ∈ ReciprocityTheory.ChartRestriction.DS.minusIdx ε, F a b * F b a :=
  ReciprocityTheory.ChartRestriction.DS.casimirK_pm ε F
