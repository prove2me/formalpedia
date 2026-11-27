-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_PrimeOpensCover_hyps_5892c7e32cc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:40.717092+00:00
-- url     : https://prove2.me/submissions/4b62f21a-91d1-4425-8791-bdf3857e1bfc

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
namespace PrimeOpensCover
theorem _root_.solution :
    (∀ p ∈ ({prime2, prime3} : Finset Nat.Primes), ¬ (p : ℕ) ∣ 5 - (p : ℕ)) ∧
    (∀ p ∈ ({prime2, prime3} : Finset Nat.Primes), ∀ q ∈ ({prime2, prime3} : Finset Nat.Primes),
      q ≠ p → (q : ℕ) ∣ 5 - (p : ℕ)) := by
  have h23 : prime2 ≠ prime3 := by
    intro h
    have := congrArg Subtype.val h
    simp [prime2, prime3] at this
  constructor
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [prime2, prime3]
  · intro p hp q hq hqp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hqp
    · simp [prime2, prime3]
    · simp [prime2, prime3]
    · exact absurd rfl hqp
end PrimeOpensCover
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
