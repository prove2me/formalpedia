-- Prove2me | solution 1 for RH.Transport.SupportedMass.finite_scaled_supported_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:29.404879+00:00
-- url     : https://prove2.me/submissions/08e813e2-10b3-4237-b0b2-5b1b658baa81

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
import Theorems.Thm_RH_Transport_SupportedMass_finite_supported_mass_le
import Theorems.Thm_RH_Transport_SupportedMass_threshold_power_identity

set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {ι : Type*} (F : Finset ι)
    (q : ι → ℝ) {a Z : ℝ} (ha : 0 < a) (hZ : 0 < Z) (ell : ℝ)
    (hsupport : ∀ i ∈ F, a * Z ^ ell ≤ q i) :
    (∑ i ∈ F, q i ^ (-2 : ℝ)) ≤
      (a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell / 2)) *
        ∑ i ∈ F, q i ^ (-(3 / 2 : ℝ)) := by
  have ht : 0 < a * Z ^ ell := mul_pos ha (Real.rpow_pos_of_pos hZ _)
  simpa only [threshold_power_identity ha hZ ell] using
    finite_supported_mass_le F q ht hsupport
end RH.Transport.SupportedMass
