-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homExp_injective_0eb9bc69d331
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:07.130323+00:00
-- url     : https://prove2.me/submissions/78bd5e77-0387-4529-8cc5-38b1963bc86b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
variable (K : Type) [Field K] (r : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution : Function.Injective (homExp r) := by
  intro a b h
  have hs : ∀ k : Fin r, a k.succ = b k.succ := fun k ↦ by
    simpa [homExp] using DFunLike.congr_fun h (Sum.inr k)
  have ht : ∑ i, a i = ∑ i, b i := by simpa [homExp] using DFunLike.congr_fun h (Sum.inl ())
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_congr rfl (fun k _ ↦ hs k)] at ht
  ext i
  refine Fin.cases ?_ (fun k ↦ hs k) i
  omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
