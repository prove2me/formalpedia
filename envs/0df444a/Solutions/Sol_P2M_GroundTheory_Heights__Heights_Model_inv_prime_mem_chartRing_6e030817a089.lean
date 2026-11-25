-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_inv_prime_mem_chartRing_6e030817a089
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:30.382141+00:00
-- url     : https://prove2.me/submissions/a54e9aee-e544-4920-9611-9ce108b42b4b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_prod_mem_chartRing_6138e0eacf84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_primeProd_eq_mul_2dccd2fab054
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37


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
variable (x o₀)
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {p : Nat.Primes} (hp : p ∈ S) (i : τ) :
    (((p : ℕ) : ℤ) : Ω)⁻¹ ∈ chartRing o₀ x i := by
  obtain ⟨hm0, hm⟩ := inv_prod_mem_chartRing x o₀ (S := S) i
  have h : (((p : ℕ) : ℤ) : Ω)⁻¹ = (primeProdErase S p : Ω) * ((primeProd S : ℤ) : Ω)⁻¹ := by
    rw [primeProd_eq_mul hp] at hm0 ⊢
    push_cast at hm0 ⊢
    have h1 : ((p : ℕ) : Ω) ≠ 0 := fun h => hm0 (by rw [h, zero_mul])
    have h2 : (primeProdErase S p : Ω) ≠ 0 := fun h => hm0 (by rw [h, mul_zero])
    field_simp
  rw [h]
  exact mul_mem (intCast_mem_chartRing x i o₀ _) hm
end GroundTheory.Heights₂.Heights.Model
