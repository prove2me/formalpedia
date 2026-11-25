-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_coeff_X_pow_mul_linear_pow_f3c190105c08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:17.504038+00:00
-- url     : https://prove2.me/submissions/21074973-372d-419a-9b68-4aaef93a198e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.GenericLinearTrdeg
namespace GroundTheory.Heights₂.Heights.GenericLinearTrdeg
theorem _root_.solution {R : Type*} [CommRing R] (e c : R) (a b D : ℕ) (h : a + b ≤ D) :
    (Polynomial.X ^ a * (Polynomial.C e * Polynomial.X + Polynomial.C c) ^ b).coeff D =
      if a + b = D then e ^ b else 0 := by
  have hlin : (Polynomial.C e * Polynomial.X + Polynomial.C c).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  split_ifs with hD
  · subst hD
    rw [Polynomial.coeff_X_pow_mul', if_pos (by omega), show a + b - a = b * 1 by omega,
      Polynomial.coeff_pow_of_natDegree_le hlin]
    simp
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc _ ≤ a + b * 1 := by
          refine (Polynomial.natDegree_mul_le).trans (add_le_add ?_ ?_)
          · exact Polynomial.natDegree_X_pow_le a
          · exact Polynomial.natDegree_pow_le_of_le b hlin
      _ < D := by omega
end GroundTheory.Heights₂.Heights.GenericLinearTrdeg
