-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_not_dvd_primeProdErase_f3d914f81af6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:42.046932+00:00
-- url     : https://prove2.me/submissions/f699b87c-a0b2-45f6-b0ed-b09b56672bd3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat

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
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (p : Nat.Primes) : ¬ ((p : ℕ) : ℤ) ∣ primeProdErase S p := by
  intro h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp p.2) _).1 h
  have : (p : ℕ) = q := (Nat.prime_dvd_prime_iff_eq p.2 q.2).1 (Int.natCast_dvd_natCast.1 hpq)
  exact (Finset.mem_erase.1 hq).1 (Subtype.ext this).symm
end GroundTheory.Heights₂.Heights.Model
