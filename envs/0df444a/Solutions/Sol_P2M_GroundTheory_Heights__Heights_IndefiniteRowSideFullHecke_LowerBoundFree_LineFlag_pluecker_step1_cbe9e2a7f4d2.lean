-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_pluecker_step1_cbe9e2a7f4d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:47.109255+00:00
-- url     : https://prove2.me/submissions/a8956887-5b8e-4ece-ada8-87e09597ef1d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_isTwValueAt_intCast_8416e01d1382

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
theorem _root_.solution (i0 : Fin 2) (z : (Σ _ : Unit, Fin 2) → ℂ) (hz0 : z ⟨(), i0⟩ ≠ 0)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 2) :
    IsPlueckerCoord DL.y (fun _ => i0) 0
      (AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1) (LinearMap.proj m))
      (Pi.basisFun Ω (Fin 2)) z (firstCols g 1 (by decide)) (g m 0) := by
  refine ⟨fun q => ((if q 0 = m then 1 else 0 : ℤ) : ℂ), fun q => ?_, ?_⟩
  · have hval : (AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1) (LinearMap.proj m))
        (Pi.basisFun Ω (Fin 2) ∘ q) = ((if q 0 = m then 1 else 0 : ℤ) : Ω) := by
      show (Pi.basisFun Ω (Fin 2) (q 0)) m = _
      rw [Pi.basisFun_apply, Pi.single_apply]
      by_cases h : q 0 = m
      · simp [h]
      · simp [h, Ne.symm h]
    rw [hval]
    exact isTwValueAt_intCast _ _ (fun _ => hz0) _
  · rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
    simp [firstCols, Equiv.funUnique]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
