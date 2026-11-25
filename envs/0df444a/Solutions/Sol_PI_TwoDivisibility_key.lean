-- Prove2me | solution 1 for PI.TwoDivisibility.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:11.115026+00:00
-- url     : https://prove2.me/submissions/77341002-1c7c-4819-a6ec-a49199a674c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerCoordinatesZero_IntCoordsZero
import Theorems.Thm_PI_TwoDivisibility_int_coords_zero
import Theorems.Thm_PI_TwoDivisibility_half_not_mem
import Theorems.Thm_PI_TwoDivisibility_zmod_pick
import Theorems.Thm_PI_TwoDivisibility_zmod_sq_self
import Theorems.Thm_PI_TwoDivisibility_two_dvd_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TwoDivisibility
namespace PI.TwoDivisibility
theorem _root_.solution (L : PeriodPair) (T : ℂ) (N : ℤ) (hN : 0 < N) (hN2 : Even N)
    (hq : T * T = T - N) (hT : ∀ w ∈ L.lattice, T * w ∈ L.lattice) :
    ∃ t : ℂ, 2 * t ∈ L.lattice ∧ T * t ∉ L.lattice ∧ (1 - T) * t ∉ L.lattice := by
  obtain ⟨a, b, ha⟩ := PeriodPair.mem_lattice.mp (hT _ L.ω₁_mem_lattice)
  obtain ⟨c, e, hc⟩ := PeriodPair.mem_lattice.mp (hT _ L.ω₂_mem_lattice)
  have h1 := int_coords_zero L (a * a + b * c - a + N) (a * b + b * e - b)
    (by push_cast; linear_combination ((a : ℂ) - 1 + T) * ha + (b : ℂ) * hc + L.ω₁ * hq)
  have h2 := int_coords_zero L (c * a + e * c - c) (c * b + e * e - e + N)
    (by push_cast; linear_combination (c : ℂ) * ha + ((e : ℂ) - 1 + T) * hc + L.ω₂ * hq)

  have htr : a + e = 1 := by
    rcases eq_or_ne b 0 with hb | hb
    · rcases eq_or_ne c 0 with hc0 | hc0
      · exfalso
        subst hb
        have h3 : a * a - a + N = 0 := by linarith [h1.1]
        have h4 : 0 ≤ a * a - a := by
          rcases le_or_gt a 0 with h | h
          · nlinarith
          · nlinarith
        linarith
      · have h5 : c * (a + e - 1) = 0 := by linear_combination h2.1
        have := (mul_eq_zero.mp h5).resolve_left hc0
        linarith
    · have h5 : b * (a + e - 1) = 0 := by linear_combination h1.2
      have := (mul_eq_zero.mp h5).resolve_left hb
      linarith

  obtain ⟨r, hr⟩ := hN2
  have hbc : ((b : ZMod 2) * (c : ZMod 2)) = 0 := by
    have h6 : ((a * a + b * c - a + N : ℤ) : ZMod 2) = 0 := by rw [h1.1]; simp
    have h7 : ((N : ℤ) : ZMod 2) = 0 := by
      rw [hr]; push_cast; rw [← two_mul]
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, zero_mul]
    push_cast at h6
    rw [h7, zmod_sq_self] at h6
    linear_combination h6
  have htr2 : ((a : ZMod 2) + (e : ZMod 2)) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod 2)) htr
    push_cast at this
    exact this
  obtain ⟨m, n, hmn1, hmn2⟩ := zmod_pick _ _ _ _ htr2 hbc
  set m' : ℤ := (m.val : ℤ) with hm'
  set n' : ℤ := (n.val : ℤ) with hn'
  have hmc : ((m' : ℤ) : ZMod 2) = m := by
    rw [hm', Int.cast_natCast, ZMod.natCast_zmod_val]
  have hnc : ((n' : ℤ) : ZMod 2) = n := by
    rw [hn', Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨(m' : ℂ) / 2 * L.ω₁ + (n' : ℂ) / 2 * L.ω₂, ?_, ?_, ?_⟩
  · exact PeriodPair.mem_lattice.mpr ⟨m', n', by ring⟩
  · have hE : T * ((m' : ℂ) / 2 * L.ω₁ + (n' : ℂ) / 2 * L.ω₂) =
        ((m' * a + n' * c : ℤ) : ℂ) / 2 * L.ω₁ + ((m' * b + n' * e : ℤ) : ℂ) / 2 * L.ω₂ := by
      push_cast
      linear_combination (-(m' : ℂ) / 2) * ha + (-(n' : ℂ) / 2) * hc
    rw [hE]
    apply half_not_mem
    rw [two_dvd_iff, two_dvd_iff]
    push_cast
    rw [hmc, hnc]
    tauto
  · have hE : (1 - T) * ((m' : ℂ) / 2 * L.ω₁ + (n' : ℂ) / 2 * L.ω₂) =
        ((m' - (m' * a + n' * c) : ℤ) : ℂ) / 2 * L.ω₁ +
          ((n' - (m' * b + n' * e) : ℤ) : ℂ) / 2 * L.ω₂ := by
      push_cast
      linear_combination ((m' : ℂ) / 2) * ha + ((n' : ℂ) / 2) * hc
    rw [hE]
    apply half_not_mem
    rw [two_dvd_iff, two_dvd_iff]
    push_cast
    rw [hmc, hnc]
    tauto
end PI.TwoDivisibility
