-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockMetricAgrees_iff_a1becd358f0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:57:44.771512+00:00
-- url     : https://prove2.me/submissions/b965851b-b4c6-4d2e-a415-4d834165912f

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
open Matrix
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {e r : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (F : HermLattice K (r + 1))
    (A : HermLine (oneBlockSizes e r)) :
    OneBlockMetricAgrees om F A ↔
      ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
        A.metric (fun _ t ↦ σ (om ((oneBlockIndex e r).symm.symm t).1 : K) *
          w ((oneBlockIndex e r).symm.symm t).2) = hermNorm (F.metric σ) w :=
  Iff.rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
