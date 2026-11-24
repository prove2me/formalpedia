-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_surjective_e0159a2963b4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:41.888442+00:00
-- url     : https://prove2.me/submissions/9c9355de-71e3-4ff3-8b3d-f02bbc326f33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesProjLattice

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
open NumberField
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesProjLattice
namespace GroundTheory.Heights₂.Heights.KLinesProjLattice
theorem _root_.solution {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) : Function.Surjective (coordProj B) := by
  unfold coordProj
  rw [LinearMap.coe_comp]
  exact (LinearMap.funLeft_surjective_of_injective K K Sum.inr Sum.inr_injective).comp
    B.equivFun.surjective
end GroundTheory.Heights₂.Heights.KLinesProjLattice
