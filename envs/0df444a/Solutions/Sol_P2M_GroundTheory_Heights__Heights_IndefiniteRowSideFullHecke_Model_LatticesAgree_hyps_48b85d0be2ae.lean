-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_LatticesAgree_hyps_48b85d0be2ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:31.443804+00:00
-- url     : https://prove2.me/submissions/b8297704-9cc8-4b00-8eca-83fddb75b7ea

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace LatticesAgree
theorem _root_.solution :
    IsIntegrallyClosed ℤ ∧ FiniteDimensional ℚ ℚ ∧ IsScalarTower ℤ ℚ ℚ ∧
    Module.Finite ℤ intLattice ∧ Module.Projective ℤ intLattice ∧
    Submodule.span ℚ (intLattice : Set ℚ) = ⊤ ∧
    (∀ p : Ideal ℤ, p.IsPrime → p.height = 1 → locSub intLattice p = locSub intLattice p) := by
  have : Module.Finite ℤ intLattice := inferInstance
  have : Module.Free ℤ intLattice := Module.free_of_finite_type_torsion_free'
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_,
    fun _ _ _ => rfl⟩
  rw [Submodule.span_span_of_tower]
  refine eq_top_iff.mpr fun y _ => ?_
  simpa only [smul_eq_mul, mul_one] using Submodule.smul_mem (Submodule.span ℚ {(1 : ℚ)}) y
    (Submodule.subset_span (Set.mem_singleton 1))
end LatticesAgree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
