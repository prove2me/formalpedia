-- Prove2me | solution 1 for RH.Transport.SupportedMass.finite_weighted_supported_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:01.000679+00:00
-- url     : https://prove2.me/submissions/725726a1-b664-46fc-937a-9988a55c8613

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
    (q w : ι → ℝ) {T : ℝ} (hT : 0 < T)
    (hw : ∀ i ∈ F, 0 ≤ w i)
    (hsupport : ∀ i ∈ F, w i ≠ 0 → T ≤ q i) :
    (∑ i ∈ F, w i * q i ^ (-2 : ℝ)) ≤
      T ^ (-(1 / 2 : ℝ)) *
        ∑ i ∈ F, w i * q i ^ (-(3 / 2 : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hwi : w i = 0
  · simp [hwi]
  · have ht := mul_le_mul_of_nonneg_left
      (supported_term_le hT (hsupport i hi hwi)) (hw i hi)
    calc
      _ ≤ w i * (T ^ (-(1 / 2 : ℝ)) * q i ^ (-(3 / 2 : ℝ))) := ht
      _ = _ := by ring
end RH.Transport.SupportedMass
