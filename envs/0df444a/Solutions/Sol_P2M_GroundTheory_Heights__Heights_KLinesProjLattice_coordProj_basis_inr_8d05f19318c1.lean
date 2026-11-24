-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_basis_inr_8d05f19318c1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:41.624631+00:00
-- url     : https://prove2.me/submissions/a1e34464-9001-4da4-b4d3-7917947d36ab

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
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (j : Fin k) :
    coordProj B (B (Sum.inr j)) = Pi.single j 1 := by
  ext i
  simp only [coordProj, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.funLeft_apply, Module.Basis.equivFun_self]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]
end GroundTheory.Heights₂.Heights.KLinesProjLattice
