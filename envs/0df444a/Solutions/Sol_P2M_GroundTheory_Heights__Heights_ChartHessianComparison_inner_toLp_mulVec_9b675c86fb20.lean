-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_inner_toLp_mulVec_9b675c86fb20
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:27.333139+00:00
-- url     : https://prove2.me/submissions/eb1f88a7-289f-46e9-86a9-2b57d669d457

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHessianComparison
variable {e : ℕ} (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
namespace GroundTheory.Heights₂.Heights.ChartHessianComparison
theorem _root_.solution (v w : Fin (e + 1) → ℂ) :
    ⟪(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1))), WithLp.toLp 2 (B *ᵥ w)⟫_ℂ =
      star v ⬝ᵥ ((Bᴴ * B) *ᵥ w) := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
end GroundTheory.Heights₂.Heights.ChartHessianComparison
