-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pointHeightDegree_hypotheses_1dbb1bf70294
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:57:49.362438+00:00
-- url     : https://prove2.me/submissions/519a6bf8-9c34-4507-8032-1159308ac9fa

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
theorem _root_.solution (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (F : HermLattice K (r + 1)) (A : HermLine (oneBlockSizes e r)) (hA : A.deg = 1)
    (hM : OneBlockMetricAgrees om F A) :
    (∀ σ, (F.metric σ).PosDef) ∧
      (∀ σ, F.metric (ComplexEmbedding.conjugate σ) = (F.metric σ).map (starRingEnd ℂ)) ∧
      (∀ u, A.deg u = 1) ∧
      ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
        A.metric (fun _ t ↦ σ (om ((oneBlockIndex e r).symm.symm t).1 : K) *
          w ((oneBlockIndex e r).symm.symm t).2) = hermNorm (F.metric σ) w :=
  ⟨F.posDef, F.conj, fun u ↦ by rw [hA]; rfl, hM⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
