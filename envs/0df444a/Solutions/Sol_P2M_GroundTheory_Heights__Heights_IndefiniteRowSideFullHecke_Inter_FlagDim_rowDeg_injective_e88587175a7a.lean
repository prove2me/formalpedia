-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_rowDeg_injective_e88587175a7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:22.024327+00:00
-- url     : https://prove2.me/submissions/9eca1236-4930-41ed-8961-ace3048ca238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_rowDeg_apply_9d47e04fac57

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution : Function.Injective (rowDeg n) := by
  intro a b h
  funext j
  have hj := j.2
  have key : ∀ c : Fin (n - 1) → ℕ,
      rowDeg n c ⟨j.val, by omega⟩ = c j + rowDeg n c ⟨j.val + 1, by omega⟩ := by
    intro c
    rw [rowDeg_apply, rowDeg_apply]
    calc (∑ k, if j.val ≤ k.val then c k else 0)
        = ∑ k, ((if j = k then c k else 0) + if j.val + 1 ≤ k.val then c k else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases h1 : j = k
          · subst h1
            simp
          · have h2 : j.val ≠ k.val := fun h => h1 (Fin.ext h)
            by_cases h3 : j.val ≤ k.val
            · rw [if_pos h3, if_neg h1, if_pos (by omega), zero_add]
            · rw [if_neg h3, if_neg h1, if_neg (by omega), add_zero]
      _ = c j + ∑ k, if j.val + 1 ≤ k.val then c k else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
          simp
  have h1 := congrFun h ⟨j.val, by omega⟩
  have h2 := congrFun h ⟨j.val + 1, by omega⟩
  rw [key a, key b, h2] at h1
  omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
