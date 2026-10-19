-- Prove2me | solution 1 for SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_shift_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/4b967c1c-fd20-4903-82b5-a4e0e7e6ddd2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_CohnElkies_LPBoundAux_summable_norm_on_translated_integral_lattice

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
namespace SpherePacking.CohnElkies.LPBoundSummability
theorem _root_.solution :
    Summable (fun ℓ : Λ => f (a + (ℓ : EuclideanSpace ℝ (Fin d)))) :=
  Summable.of_norm (summable_norm_on_translated_integral_lattice (Λ := Λ) f a)
end SpherePacking.CohnElkies.LPBoundSummability
