-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_monic_of_coeffs_c20b2a3a7093
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:57.366891+00:00
-- url     : https://prove2.me/submissions/9b19f1b5-c4bb-4a1b-9804-c2c76ee6e1cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StGrowthOffHypersurfacePolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPieceRootProductPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PieceRootProductPolynomial
theorem _root_.solution {R : Type*} [CommRing R] (k : ℕ) (p : ℕ → R)
    (i : ℕ) :
    (Polynomial.X ^ k + ∑ j : Fin k, Polynomial.C (p j) * Polynomial.X ^ (j : ℕ)).coeff i =
      if i < k then p i else if i = k then 1 else 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hi : i < k
  · rw [Finset.sum_eq_single ⟨i, hi⟩, if_neg hi.ne, if_pos rfl, if_pos hi, zero_add]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext h.symm)
    · simp
  · rw [Finset.sum_eq_zero, if_neg hi, add_zero]
    intro j _
    rw [if_neg]
    intro h
    exact hi (h ▸ j.isLt)
end PieceRootProductPolynomial
end GroundTheory.Heights₂.Heights.HilbertSamuel
