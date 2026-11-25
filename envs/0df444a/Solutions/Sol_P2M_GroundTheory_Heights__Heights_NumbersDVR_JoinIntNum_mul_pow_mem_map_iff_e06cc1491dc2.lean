-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mul_pow_mem_map_iff_e06cc1491dc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:24:31.629883+00:00
-- url     : https://prove2.me/submissions/6bb90f65-93c0-406e-8d26-e4ad47e6a5b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_rename_b30606b9ed68

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
theorem _root_.solution (V : Ideal (MRing ι F)) (f : MRing ι F) (t : ℕ) :
    rename (liftVar (ι := ι) ptIdx) f * X newVar ^ t ∈ V.map (rename (liftVar (ι := ι) ptIdx)) ↔
      f ∈ V := by
  constructor
  · intro h
    have hle : V.map (rename (liftVar (ι := ι) ptIdx)) ≤ V.comap (aeval (dropPt F)) :=
      Ideal.map_le_iff_le_comap.mpr fun x hx => by
        rw [Ideal.mem_comap, Ideal.mem_comap, dropPt_rename]
        exact hx
    have h2 := hle h
    rw [Ideal.mem_comap, map_mul, map_pow, dropPt_rename, aeval_X] at h2
    simpa [newVar, dropPt] using h2
  · intro h
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h)
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
