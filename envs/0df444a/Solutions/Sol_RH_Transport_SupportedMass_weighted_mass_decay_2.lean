-- Prove2me | solution 2 for RH.Transport.SupportedMass.weighted_mass_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:54.482439+00:00
-- url     : https://prove2.me/submissions/1b9d2575-a445-4441-a8b2-e9330c8a5f70

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
import Theorems.Thm_RH_Transport_SupportedMass_finite_weighted_supported_mass_le
import Theorems.Thm_RH_Transport_SupportedMass_threshold_power_identity

set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {ι : Type*} (F : Finset ι)
    (q w : ι → ℝ) {a Z C ell : ℝ}
    (ha : 0 < a) (hZ : 0 < Z)
    (hw : ∀ i ∈ F, 0 ≤ w i)
    (hsupport : ∀ i ∈ F, w i ≠ 0 → a * Z ^ ell ≤ q i)
    (hmass : (∑ i ∈ F, w i * q i ^ (-(3 / 2 : ℝ))) ≤ C) :
    (∑ i ∈ F, w i * q i ^ (-2 : ℝ)) ≤
      (C * a ^ (-(1 / 2 : ℝ))) * Z ^ (-ell / 2) := by
  have ht : 0 < a * Z ^ ell := mul_pos ha (Real.rpow_pos_of_pos hZ _)
  calc
    _ ≤ (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) *
        ∑ i ∈ F, w i * q i ^ (-(3 / 2 : ℝ)) :=
      finite_weighted_supported_mass_le F q w ht hw hsupport
    _ ≤ (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) * C :=
      mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg ht.le _)
    _ = _ := by
      rw [threshold_power_identity ha hZ ell]
      ring
end RH.Transport.SupportedMass
