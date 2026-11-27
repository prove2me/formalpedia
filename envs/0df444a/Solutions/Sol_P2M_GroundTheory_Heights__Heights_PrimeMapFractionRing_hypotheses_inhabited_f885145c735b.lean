-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeMapFractionRing_hypotheses_inhabited_f885145c735b
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:09.751206+00:00
-- url     : https://prove2.me/submissions/f54d63f3-999c-4a6e-baa5-746a3276b575

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
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
noncomputable section
theorem _root_.solution :
    Prime (X 0 : MvPolynomial (Fin 1) ℤ) ∧ ∀ a : ℤ, (X 0 : MvPolynomial (Fin 1) ℤ) ≠ C a := by
  refine ⟨MvPolynomial.X_prime, fun a h => ?_⟩
  have := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) h
  rw [MvPolynomial.coeff_X', MvPolynomial.coeff_C, if_pos rfl, if_neg] at this
  · exact one_ne_zero this
  · exact (Finsupp.single_ne_zero.2 one_ne_zero).symm



