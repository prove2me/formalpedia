-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.quadInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:46.154168+00:00
-- url     : https://prove2.me/submissions/fe75e1aa-1525-4b31-8b9a-3c28cee63212

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQuadInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_omegaK_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KQ_mem_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ratInt_of_isIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_conj_sqD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (x : 𝓞 (KQ d)) :
    ∃ a b : ℤ, (((x : KQ d) : ℂ)) = a + b * omegaK d := by
  have hx : IsIntegral ℤ (((x : KQ d) : ℂ)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map (IntermediateField.val (KQ d)).toRingHom.toIntAlgHom
  obtain ⟨u, v, huv⟩ := (KQ_mem_iff d _).mp (x : KQ d).2
  rw [huv] at hx
  have hc : IsIntegral ℤ ((starRingEnd ℂ) ((u : ℂ) + v * sqD d)) := hx.map (starRingEnd ℂ).toIntAlgHom
  rw [map_add, map_mul, conj_sqD, map_ratCast, map_ratCast] at hc
  have hs := sqD_sq d
  obtain ⟨A, hA⟩ := ratInt_of_isIntegral (q := 2 * u) (by
    have e : (((2 * u : ℚ)) : ℂ) = ((u : ℂ) + v * sqD d) + ((u : ℂ) + v * -sqD d) := by
      push_cast; ring
    rw [e]; exact hx.add hc)
  obtain ⟨N, hN⟩ := ratInt_of_isIntegral (q := u ^ 2 + d * v ^ 2) (by
    have e : (((u ^ 2 + d * v ^ 2 : ℚ)) : ℂ) = ((u : ℂ) + v * sqD d) * ((u : ℂ) + v * -sqD d) := by
      push_cast; linear_combination ((v : ℂ) ^ 2) * hs
    rw [e]; exact hx.mul hc)

  have hd0 : (d : ℤ) ≠ 0 := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℚ) * (2 * v) = k := by
    set r : ℚ := (d : ℚ) * (2 * v) with hr
    have hr2 : r ^ 2 = ((d * (4 * N - A ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [← hN, ← hA]; ring
    have hden : r.den = 1 := by
      have := congrArg Rat.den hr2
      rw [Rat.den_pow, Rat.den_intCast] at this
      exact (Nat.pow_eq_one.mp this).resolve_right (by norm_num)
    exact ⟨r.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩
  have hk2 : k ^ 2 = d * (4 * N - A ^ 2) := by
    have : ((k ^ 2 : ℤ) : ℚ) = ((d * (4 * N - A ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [← hk, ← hN, ← hA]; ring
    exact_mod_cast this
  have hdk : (d : ℤ) ∣ k := by
    have hsq : Squarefree (d : ℤ) := Int.squarefree_natCast.mpr hsf
    exact (hsq.dvd_pow_iff_dvd (n := 2) (by norm_num)).mp ⟨_, hk2⟩
  obtain ⟨B, rfl⟩ := hdk
  have hB : 2 * v = B := by
    have : (d : ℚ) * (2 * v) = (d : ℚ) * B := by rw [hk]; push_cast; ring
    exact mul_left_cancel₀ (by exact_mod_cast hd0) this

  have h4 : A ^ 2 + (d : ℤ) * B ^ 2 = 4 * N := by
    have : ((A ^ 2 + (d : ℤ) * B ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [← hN, ← hA, ← hB]; ring
    exact_mod_cast this
  obtain ⟨c, hc3⟩ : ∃ c : ℤ, (d : ℤ) = 4 * c + 3 := ⟨(d / 4 : ℕ), by omega⟩
  obtain ⟨a, ha | ha⟩ := Int.even_or_odd' A <;> obtain ⟨b, hb | hb⟩ := Int.even_or_odd' B
  · refine ⟨a - b, B, ?_⟩
    rw [omegaK_eq]
    have e1 : (u : ℂ) = ((A : ℚ) : ℂ) / 2 := by rw [← hA]; push_cast; ring
    have e2 : (v : ℂ) = ((B : ℚ) : ℂ) / 2 := by rw [← hB]; push_cast; ring
    rw [huv, e1, e2, ha, hb]; push_cast; ring
  · exfalso
    rw [ha, hb, hc3] at h4
    have : 4 * N = 4 * (a ^ 2 + 4 * c * b ^ 2 + 4 * c * b + c + 3 * b ^ 2 + 3 * b) + 3 := by
      rw [← h4]; ring
    omega
  · exfalso
    rw [ha, hb, hc3] at h4
    have : 4 * N = 4 * (a ^ 2 + a + 4 * c * b ^ 2 + 3 * b ^ 2) + 1 := by
      rw [← h4]; ring
    omega
  · refine ⟨a - b, B, ?_⟩
    rw [omegaK_eq]
    have e1 : (u : ℂ) = ((A : ℚ) : ℂ) / 2 := by rw [← hA]; push_cast; ring
    have e2 : (v : ℂ) = ((B : ℚ) : ℂ) / 2 := by rw [← hB]; push_cast; ring
    rw [huv, e1, e2, ha, hb]; push_cast; ring
end ReciprocityTheory.ChartRestriction.L1
