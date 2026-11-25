-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_prime_mem_of_isMaximal_5d839b2c56a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:21.988917+00:00
-- url     : https://prove2.me/submissions/4d123bc4-6438-44a4-82b7-f13cb04b8250

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isJacobsonRing_int_5cab28bc29cb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (A : Type*) [CommRing A] [Algebra.FiniteType ℤ A]
    (𝔪 : Ideal A) [𝔪.IsMaximal] : ∃ p : ℕ, p.Prime ∧ (p : A) ∈ 𝔪 := by
  let _ := Ideal.Quotient.field 𝔪
  have := isJacobsonRing_int
  have : Algebra.FiniteType ℤ (A ⧸ 𝔪) := inferInstance
  have : Module.Finite ℤ (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ 𝔪)
  obtain ⟨p, hp⟩ := CharP.exists (A ⧸ 𝔪)
  rcases CharP.char_is_prime_or_zero (A ⧸ 𝔪) p with hp' | rfl
  · refine ⟨p, hp', ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  · exfalso
    have : CharZero (A ⧸ 𝔪) := CharP.charP_to_charZero (A ⧸ 𝔪)
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ) (⊥ : Ideal (A ⧸ 𝔪))
    have hbot : (⊥ : Ideal (A ⧸ 𝔪)).comap (algebraMap ℤ (A ⧸ 𝔪)) = ⊥ := by
      rw [← RingHom.ker_eq_comap_bot, RingHom.ker_eq_bot_iff_eq_zero]
      intro n hn
      exact_mod_cast (show ((n : ℤ) : A ⧸ 𝔪) = 0 by simpa using hn)
    rw [hbot] at hmax
    exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr hmax)
end GroundTheory.Heights₂.Heights.Model
