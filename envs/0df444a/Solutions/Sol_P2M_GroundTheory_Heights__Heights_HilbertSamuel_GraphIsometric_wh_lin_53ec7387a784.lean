-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_wh_lin_53ec7387a784
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:39.474823+00:00
-- url     : https://prove2.me/submissions/2bb96e87-64dc-4ea8-b21e-f98378d3d19e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
theorem _root_.solution [DecidableEq K] (A : ∀ k, ι₂ k → ι k → ℤ) (q : Σ k, ι₂ k) :
    IsWeightedHomogeneous (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (Sum.elim ι ι₂))
      (rename inlV (linForm A q)) (Pi.single (Sum.inl q.1) 1) := by
  rw [← mem_weightedHomogeneousSubmodule]
  simp only [linForm, map_sum, map_mul, rename_C, rename_X]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_X ℤ _ _))
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
