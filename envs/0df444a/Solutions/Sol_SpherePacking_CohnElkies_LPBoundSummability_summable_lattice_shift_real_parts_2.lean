-- Prove2me | solution 2 for SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_shift_real_parts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:06:15.769803+00:00
-- url     : https://prove2.me/submissions/ac95d86b-bd2c-4983-bd72-e2bcf11b6ff2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators
open scoped SchwartzMap
open SpherePacking SpherePacking.CohnElkies
variable {d : ℕ}
open SpherePacking.CohnElkies.LPBoundSummability
open SpherePacking.CohnElkies.LPBoundAux
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (a : EuclideanSpace ℝ (Fin d))


theorem solution :
    Summable (fun ℓ : Λ => (f (a + (ℓ : EuclideanSpace ℝ (Fin d)))).re) := by
  have hS : Summable (fun ℓ : Λ => f (a + (ℓ : EuclideanSpace ℝ (Fin d)))) := by
    obtain ⟨C, hCpos, hC⟩ := f.decay (Module.finrank ℤ Λ + 1) 0
    have hC' : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ (Module.finrank ℤ Λ + 1) * ‖f x‖ ≤ C := by
      simpa [norm_iteratedFDeriv_zero] using! hC
    refine Summable.of_norm_bounded_eventually
      ((ZLattice.summable_norm_sub_inv_pow Λ (Module.finrank ℤ Λ + 1) (by omega) (-a)).mul_left C) ?_
    have hfin : {ℓ : Λ | (ℓ : EuclideanSpace ℝ (Fin d)) = -a}.Finite :=
      Set.Subsingleton.finite (fun x hx y hy => Subtype.ext (hx.trans hy.symm))
    filter_upwards [hfin.compl_mem_cofinite] with ℓ hℓ
    have hne : (ℓ : EuclideanSpace ℝ (Fin d)) - -a ≠ 0 := by
      intro h; apply hℓ; exact sub_eq_zero.mp h
    have hpos : 0 < ‖(ℓ : EuclideanSpace ℝ (Fin d)) - -a‖ := norm_pos_iff.mpr hne
    have h1 := hC' (a + ℓ)
    rw [show a + (ℓ : EuclideanSpace ℝ (Fin d)) = (ℓ : EuclideanSpace ℝ (Fin d)) - -a by abel] at h1
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rw [show a + (ℓ : EuclideanSpace ℝ (Fin d)) = (ℓ : EuclideanSpace ℝ (Fin d)) - -a by abel]
    linarith [mul_comm (‖(ℓ : EuclideanSpace ℝ (Fin d)) - -a‖ ^ (Module.finrank ℤ Λ + 1))
      ‖f ((ℓ : EuclideanSpace ℝ (Fin d)) - -a)‖]
  simpa using Complex.reCLM.summable hS

