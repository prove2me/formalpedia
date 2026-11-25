-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_mapDomain_fst_cfb4929795a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:04.296595+00:00
-- url     : https://prove2.me/submissions/8bd9b3dc-a9ac-4316-8ed0-cd7a75557aca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.CoordinateConeArithVar
theorem _root_.solution [DecidableEq K] (e : (Σ k, ι k) →₀ ℕ) :
    ⇑(e.mapDomain Sigma.fst) = Finsupp.weight (NumbersDVR.blockWeight ι) e := by
  ext k
  rw [Finsupp.mapDomain, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finsupp.finsetSum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp [NumbersDVR.blockWeight, Finsupp.single_apply, Pi.single_apply, eq_comm]
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
