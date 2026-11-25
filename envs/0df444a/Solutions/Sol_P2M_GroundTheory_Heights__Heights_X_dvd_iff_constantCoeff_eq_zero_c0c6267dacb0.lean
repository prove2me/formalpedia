-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_X_dvd_iff_constantCoeff_eq_zero_c0c6267dacb0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:24:55.60459+00:00
-- url     : https://prove2.me/submissions/f94c7927-d64c-4c61-8cf9-80f5c20f5c6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin 1 × Fin 1) R) : X (0, 0) ∣ f ↔ constantCoeff f = 0 := by
  rw [X_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h
    have h0 := congrArg (coeff 0) h
    rw [coeff_modMonomial_of_not_le _ (by simp)] at h0
    simpa [constantCoeff_eq] using h0
  · intro h
    ext s
    rw [coeff_zero]
    by_cases hs : Finsupp.single ((0 : Fin 1), (0 : Fin 1)) 1 ≤ s
    · exact coeff_modMonomial_of_le _ hs
    · rw [coeff_modMonomial_of_not_le _ hs]
      have hs0 : s = 0 := by
        ext ij
        obtain rfl : ij = (0, 0) := Subsingleton.elim _ _
        by_contra hne
        exact hs (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hne))
      rw [hs0]
      simpa [constantCoeff_eq] using h
end GroundTheory.Heights₂.Heights
