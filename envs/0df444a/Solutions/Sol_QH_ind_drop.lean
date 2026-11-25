-- Prove2me | solution 1 for QH.ind_drop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:01:59.842347+00:00
-- url     : https://prove2.me/submissions/f4b5a422-6478-4c9d-bdcf-a4aff1dfce17

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_TwistPrim
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_IndUnique
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_IndDrop
import Theorems.Thm_QH_ind_unique
import Theorems.Thm_QH_twist_prim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∀ (N₀ q M : ℕ) (ξ : DirichletCharacter ℂ N₀) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 0 < N₀ → q.Prime → q ≠ 2 → ¬ q ∣ N₀ → M ≠ 0 →
      Ind χ (fun n => ξ n * J q n) M → Ind χ (fun n => ξ n * J q n) (N₀ * q) := by
  intro N₀ q M ξ N _ χ hN₀ hq hq2 hqN₀ hM hχ
  obtain ⟨hχp, hind⟩ := hχ
  haveI : NeZero N₀ := ⟨hN₀.ne'⟩
  haveI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hqf : ¬ q ∣ ξ.conductor := fun h => hqN₀ (h.trans ξ.conductor_dvd_level)
  obtain ⟨ψ, hψ, -, hψeq⟩ :=
    twist_prim ξ.conductor q ξ.primitiveCharacter ξ.primitiveCharacter_isPrimitive hq hq2 hqf
  have hprim : ∀ n : ℕ, n.Coprime N₀ → ξ n = ξ.primitiveCharacter n := by
    intro n hn
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ.primitiveCharacter
      ξ.conductor_dvd_level (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    rw [Int.cast_natCast, Int.cast_natCast] at h
    exact h
  have heq := ind_unique N (ξ.conductor * q) (M * N₀ * q) χ ψ
    (mul_ne_zero (mul_ne_zero hM hN₀.ne') hq.ne_zero) hχp hψ (fun n hn => by
      rw [hind n (Nat.Coprime.coprime_dvd_right (Dvd.intro (N₀ * q) (by ring)) hn), hψeq]
      dsimp only
      rw [hprim n (Nat.Coprime.coprime_dvd_right (Dvd.intro (M * q) (by ring)) hn)])
  obtain ⟨hN, hχψ⟩ := Sigma.mk.inj_iff.1 heq
  subst hN
  have hc : χ = ψ := eq_of_heq hχψ
  subst hc
  refine ⟨hχp, fun n hn => ?_⟩
  rw [hψeq]
  dsimp only
  rw [hprim n (Nat.Coprime.coprime_dvd_right (dvd_mul_right N₀ q) hn)]
end QH
