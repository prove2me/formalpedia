-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicJacobianNeZero_det_fin_one_8fe152a841bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:35.330324+00:00
-- url     : https://prove2.me/submissions/c7640046-6b53-4357-94b9-f0e39bca21ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicJacobianNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicDerivNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicKernelFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalFlatNotInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicJacobianNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Filter Topology
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero
theorem _root_.solution (A : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) : LinearMap.det A = A 1 0 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 1)), Matrix.det_unique, LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply, Pi.basisFun_repr]
  have h1 : (Pi.single (default : Fin 1) (1 : ℂ) : Fin 1 → ℂ) = 1 := by
    funext i
    fin_cases i
    rfl
  rw [h1]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero
