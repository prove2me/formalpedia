-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_map_secLin_2dea74a05335
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:24:40.090389+00:00
-- url     : https://prove2.me/submissions/7e164958-123a-432d-8b31-232e79e89c49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBLinInj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] {n e : ℕ}
    {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R} {Q' : Ideal (MvPolynomial (Fin n) S)}
    {y' : Par e n → S} (ψ : SecAlg Q y →+* SecAlg Q' y') (c : R →+* S)
    (hc : ∀ j, ψ (secCoord Q y j) = secCoord Q' y' j)
    (hr : ∀ r : R, ψ (algebraMap R _ r) = algebraMap S _ (c r)) (w : Fin n → R) :
    ψ (secLin Q y w) = secLin Q' y' (fun j => c (w j)) := by
  simp only [secLin, linForm, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (Ideal.Quotient.mk (secIdeal Q y) (C (w j))) = algebraMap R (SecAlg Q y) (w j) := rfl
  have h2 : (Ideal.Quotient.mk (secIdeal Q' y') (C (c (w j)))) = algebraMap S (SecAlg Q' y') (c (w j)) :=
    rfl
  rw [h1, h2, hr]
  exact congrArg _ (hc j)
end GroundTheory.Heights₂.Heights.Vertical
