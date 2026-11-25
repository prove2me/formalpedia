-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.capelliC_negT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:42.617421+00:00
-- url     : https://prove2.me/submissions/ad4d67a1-22a2-4a46-9bac-31ec00b19326

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
theorem _root_.solution {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] (E : Fin n → Fin n → 𝒰) (x : ℂ) :
    capelliC (fun a b => -E b a) x = (-1) ^ n * rminor E id id ((n : ℂ) - 1 - x) := by
  unfold capelliC cminor rminor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← (Int.cast_commute _ _).eq, mul_assoc]
  congr 1
  have hf : (fun j : Fin n => capEntry (fun a b => -E b a) (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j)) =
      Neg.neg ∘ fun j : Fin n => capEntry E ((n : ℂ) - 1 - x - ((n : ℕ) : ℂ) + 1 + ((j : ℕ) : ℂ)) (id j)
        (id (σ j)) := by
    funext j
    simp only [capEntry, id, Function.comp]
    by_cases h : σ j = j
    · simp only [h, if_true]
      rw [neg_add, ← map_neg]
      congr 2
      ring
    · have h' : ¬ j = σ j := fun e => h e.symm
      simp only [if_neg h, if_neg h', add_zero]
  rw [hf, ← List.map_ofFn, List.prod_map_neg, List.length_ofFn]
end ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
