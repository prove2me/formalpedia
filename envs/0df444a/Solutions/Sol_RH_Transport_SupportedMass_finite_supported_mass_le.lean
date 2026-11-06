-- Prove2me | solution 1 for RH.Transport.SupportedMass.finite_supported_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:00.347191+00:00
-- url     : https://prove2.me/submissions/f60238d5-cfdd-4297-b62f-da1aed065ac7

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
import Theorems.Thm_RH_Transport_SupportedMass_supported_term_le

set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {ι : Type*} (F : Finset ι)
    (q : ι → ℝ) {T : ℝ} (hT : 0 < T)
    (hsupport : ∀ i ∈ F, T ≤ q i) :
    (∑ i ∈ F, q i ^ (-2 : ℝ)) ≤
      T ^ (-(1 / 2 : ℝ)) * ∑ i ∈ F, q i ^ (-(3 / 2 : ℝ)) := by
  calc
    _ ≤ ∑ i ∈ F, T ^ (-(1 / 2 : ℝ)) * q i ^ (-(3 / 2 : ℝ)) :=
      Finset.sum_le_sum (fun i hi => supported_term_le hT (hsupport i hi))
    _ = _ := (Finset.mul_sum ..).symm
end RH.Transport.SupportedMass
