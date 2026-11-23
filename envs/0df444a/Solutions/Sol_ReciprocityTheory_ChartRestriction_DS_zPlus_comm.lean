-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.zPlus_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:24.267498+00:00
-- url     : https://prove2.me/submissions/d1f15dda-ef42-4370-a0ea-e4152e4f0126

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB

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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    zPlus ε E * E a b = E a b * zPlus ε E +
      ((if ε a = true then (1 : ℂ) else 0) - (if ε b = true then (1 : ℂ) else 0)) • E a b := by
  have key : ∀ c, E c c * E a b = E a b * E c c +
      ((if c = a then (1 : ℂ) else 0) - (if b = c then (1 : ℂ) else 0)) • E a b := by
    intro c
    rw [← sub_eq_iff_eq_add', hE c c a b]
    rcases eq_or_ne c a with rfl | h1 <;> rcases eq_or_ne b c with rfl | h2 <;> simp [*, sub_smul]
  unfold zPlus
  rw [Finset.sum_mul, Finset.sum_congr rfl (fun c _ => key c), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_smul]
  congr 2
  simp [Finset.sum_sub_distrib, plusIdx]
end ReciprocityTheory.ChartRestriction.DS
