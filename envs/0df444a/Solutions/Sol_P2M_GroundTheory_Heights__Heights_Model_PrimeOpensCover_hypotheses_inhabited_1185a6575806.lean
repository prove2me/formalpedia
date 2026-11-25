-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_hypotheses_inhabited_1185a6575806
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:09.910045+00:00
-- url     : https://prove2.me/submissions/01a68860-1280-4f2e-80e3-b48bee965484

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
namespace PrimeOpensCover
theorem _root_.solution :
    (∀ p ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes),
      ¬ ((p : ℕ) : ℤ) ∣ (if (p : ℕ) = 2 then 3 else 2)) ∧
    (∀ p ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes),
      ∀ q ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes), q ≠ p →
        ((q : ℕ) : ℤ) ∣ (if (p : ℕ) = 2 then 3 else 2)) := by
  have mem : ∀ p ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes),
      (p : ℕ) = 2 ∨ (p : ℕ) = 3 := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Or.inl rfl
    · rw [Finset.mem_singleton.mp hp]
      exact Or.inr rfl
  refine ⟨fun p hp => ?_, fun p hp q hq hne => ?_⟩
  · rcases mem p hp with h | h <;> rw [h] <;> norm_num
  · have hne' : (q : ℕ) ≠ p := fun h => hne (Subtype.ext h)
    rcases mem p hp with h | h <;> rcases mem q hq with h' | h'
    · exact absurd (h'.trans h.symm) hne'
    · rw [h, h']
      norm_num
    · rw [h, h']
      norm_num
    · exact absurd (h'.trans h.symm) hne'
end PrimeOpensCover
end GroundTheory.Heights₂.Heights.Model
