-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SumCp_hyps_7865e4e12e13
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:06.223829+00:00
-- url     : https://prove2.me/submissions/268106ca-91ad-404d-8a8f-014beacb500e

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
theorem _root_.solution : (1 : ℤ) ≠ 0 ∧ (2 : ℝ) ≤ 3 ∧ ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime ∧ (p : ℝ) ≤ 3 := by
  refine ⟨one_ne_zero, by norm_num, ?_⟩
  intro p hp
  simp at hp
  rcases hp with rfl | rfl
  · exact ⟨Nat.prime_two, by norm_num⟩
  · exact ⟨Nat.prime_three, by norm_num⟩



