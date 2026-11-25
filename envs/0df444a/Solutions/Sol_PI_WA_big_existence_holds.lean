-- Prove2me | solution 1 for PI.WA.big_existence_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:11.886551+00:00
-- url     : https://prove2.me/submissions/087f8cee-dc82-44d8-93aa-85689a867005

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
import Theorems.Thm_PI_WA_g_big_pow_mul
import Theorems.Thm_PI_WA_g_small_pow_mul
import Theorems.Thm_PI_WA_g_int_pow_mul
import Theorems.Thm_PI_WA_g_B_big
import Theorems.Thm_PI_WA_g_B_small
import Theorems.Thm_PI_WA_g_B_bigj
import Theorems.Thm_PI_WADVR_Sm_alg
import Theorems.Thm_PI_WADVR_Sm_mono
import Theorems.Thm_PI_WADVR_Sm_mul
import Theorems.Thm_PI_WADVR_Sm_pow
import Theorems.Thm_PI_WADVR_big_of_not_mem
import Theorems.Thm_PI_WADVR_one_add_of_sm
import Theorems.Thm_PI_WADVR_sm_exists
import Theorems.Thm_PI_WADVR_sm_natCast
import Theorems.Thm_PI_WADVR_sm_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WA
open PI.WADVR
namespace PI.WA
theorem _root_.solution : BigExists := by
  intro E _ ι _ W Q _ _ _ _ _ _ iw p hp0 hpu hden hdist ϖ hϖ i
  classical

  have pair : ∀ j, j ≠ i → ∃ y : E, y ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i y)⁻¹ ∧
      Sm (Q j) (ϖ j) 1 (iw j y) := by
    intro j hji
    obtain ⟨a, haj, hai⟩ := hdist j i hji
    obtain ⟨b, hbi, hbj⟩ := hdist i j (Ne.symm hji)
    obtain ⟨hai0, hai1⟩ := big_of_not_mem (hϖ i) hai
    obtain ⟨hbj0, hbj1⟩ := big_of_not_mem (hϖ j) hbj
    have ha0 : a ≠ 0 := fun h => hai0 (by rw [h, map_zero])
    have hb0 : b ≠ 0 := fun h => hbj0 (by rw [h, map_zero])
    refine ⟨a * b⁻¹, mul_ne_zero ha0 (inv_ne_zero hb0), ?_, ?_⟩
    · have e : (iw i (a * b⁻¹))⁻¹ = iw i b * (iw i a)⁻¹ := by
        rw [map_mul, map_inv₀, mul_inv, inv_inv, mul_comm]
      rw [e]
      have := ((sm_zero_iff (ϖ := ϖ i)).mpr hbi).mul (hϖ i) hai1
      rwa [zero_add] at this
    · have e : iw j (a * b⁻¹) = iw j a * (iw j b)⁻¹ := by rw [map_mul, map_inv₀]
      rw [e]
      have := ((sm_zero_iff (ϖ := ϖ j)).mpr haj).mul (hϖ j) hbj1
      rwa [zero_add] at this

  have base : ∃ z : E, z ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i z)⁻¹ := by
    obtain ⟨a, c, hac⟩ := hden i ((p : Q i)⁻¹) 1
    have hpi := hp0 i
    have hts : Sm (Q i) (ϖ i) 1 ((p : Q i) ^ 2 * algebraMap (W i) (Q i) c) := by
      have h1 := ((sm_natCast (Q := Q i) (hϖ i) (hpu i)).pow (hϖ i) 2).mul (hϖ i)
        (Sm.alg (ϖ := ϖ i) (Q := Q i) c)
      exact h1.mono (hϖ i) (by norm_num)
    obtain ⟨h1t, h2t⟩ := one_add_of_sm (hϖ i) hts
    have e : iw i a = (p : Q i)⁻¹ * (1 + (p : Q i) ^ 2 * algebraMap (W i) (Q i) c) := by
      rw [hac]
      field_simp
    refine ⟨a, fun h => ?_, ?_⟩
    · rw [h, map_zero] at e
      exact mul_ne_zero (inv_ne_zero hpi) h1t e.symm
    · rw [e, mul_inv, inv_inv]
      have := (sm_natCast (Q := Q i) (hϖ i) (hpu i)).mul (hϖ i) h2t
      rwa [add_zero] at this

  have main : ∀ S : Finset ι, ∃ z : E, z ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i z)⁻¹ ∧
      ∀ k ∈ S, k ≠ i → Sm (Q k) (ϖ k) 1 (iw k z) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨z, hz, hzi⟩ := base
      exact ⟨z, hz, hzi, by simp⟩
    | @insert j S hjS ih =>
      obtain ⟨z, hz0, hzi, hzS⟩ := ih
      by_cases hji : j = i
      · refine ⟨z, hz0, hzi, fun k hk hki => hzS k ?_ hki⟩
        exact (Finset.mem_insert.mp hk).resolve_left (fun h => hki (h.trans hji))
      · obtain ⟨y, hy0, hyi, hyj⟩ := pair j hji
        choose m hm using fun k => sm_exists (hϖ k) (iw k y)
        obtain ⟨r, hr1, hrm⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ k, 1 ≤ (r : ℤ) + m k := by
          refine ⟨1 + ∑ k, (-(m k)).toNat, by omega, fun k => ?_⟩
          have h1 : (-(m k)).toNat ≤ ∑ k, (-(m k)).toNat :=
            Finset.single_le_sum (f := fun k => (-(m k)).toNat) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
          have h2 := Int.self_le_toNat (-(m k))
          have h3 : ((1 + ∑ k, (-(m k)).toNat : ℕ) : ℤ) ≥ 1 + ((-(m k)).toNat : ℤ) := by
            exact_mod_cast Nat.add_le_add_left h1 1
          linarith
        have hzi0 : iw i z ≠ 0 := (map_ne_zero _).mpr hz0
        by_cases hzj : iw j z ∈ Set.range (algebraMap (W j) (Q j))
        · refine ⟨z ^ r * y, mul_ne_zero (pow_ne_zero _ hz0) hy0, ?_, ?_⟩
          · rw [map_mul, map_pow]
            exact g_big_pow_mul (hϖ i) hzi hyi r
          · intro k hk hki
            rw [map_mul, map_pow]
            rcases Finset.mem_insert.mp hk with h | hkS
            · rw [h]
              exact g_int_pow_mul (hϖ j) ((sm_zero_iff (ϖ := ϖ j)).mpr hzj) hyj r
            · exact g_small_pow_mul (hϖ k) (hzS k hkS hki) (hm k) r (hrm k)
        · obtain ⟨hzj0, hzj1⟩ := big_of_not_mem (hϖ j) hzj
          obtain ⟨hd, hbig⟩ := g_B_big (hϖ i) hzi0 hzi ((map_ne_zero _).mpr hy0) hyi hr1
          have hmap : ∀ k, iw k (z ^ r * (1 + z ^ r)⁻¹ * y) =
              (iw k z) ^ r * (1 + (iw k z) ^ r)⁻¹ * iw k y := fun k => by
            simp only [map_mul, map_pow, map_inv₀, map_add, map_one]
          have hd' : (1 + z ^ r : E) ≠ 0 := fun h => hd (by
            have : iw i (1 + z ^ r) = 1 + (iw i z) ^ r := by
              simp only [map_add, map_one, map_pow]
            rw [← this, h, map_zero])
          refine ⟨z ^ r * (1 + z ^ r)⁻¹ * y,
            mul_ne_zero (mul_ne_zero (pow_ne_zero _ hz0) (inv_ne_zero hd')) hy0, ?_, ?_⟩
          · rw [hmap]
            exact hbig
          · intro k hk hki
            rw [hmap]
            rcases Finset.mem_insert.mp hk with h | hkS
            · rw [h]
              exact g_B_bigj (hϖ j) hzj0 hzj1 hyj hr1
            · exact g_B_small (hϖ k) (hzS k hkS hki) (hm k) hr1 (hrm k)
  obtain ⟨z, hz0, hzi, hzS⟩ := main Finset.univ
  exact ⟨z, hz0, hzi, fun j hj => hzS j (Finset.mem_univ j) hj⟩
end PI.WA
