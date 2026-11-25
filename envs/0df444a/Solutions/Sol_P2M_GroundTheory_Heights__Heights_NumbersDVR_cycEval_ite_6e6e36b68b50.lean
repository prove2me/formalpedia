-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_ite_6e6e36b68b50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:40.866449+00:00
-- url     : https://prove2.me/submissions/71c1ba12-bd92-4e41-afb2-f7b65876cbd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalCongrOnSupport

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
universe u
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
omit [Fintype K] [DecidableEq K]
open Classical
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (p : Ideal (MRing ι R) → Prop) (A B : Ideal (MRing ι R) → ℤ)
    (Z : Ideal (MRing ι R) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => if p W then A W else B W) Z =
      cycEval (fun W => if p W then A W else 0) Z + cycEval (fun W => if p W then 0 else B W) Z := by
  unfold cycEval
  rw [← finsum_add_distrib (hZ.subset (Function.support_mul_subset_left _ _))
    (hZ.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  dsimp only
  split_ifs <;> ring
end GroundTheory.Heights₂.Heights.NumbersDVR
