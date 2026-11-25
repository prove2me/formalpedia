-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_specFirst_map_0340cfe6fa1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:02.907969+00:00
-- url     : https://prove2.me/submissions/fb9b0e3e-44e3-45ad-b21c-010f97e7999f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussEq

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
theorem _root_.solution {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {n k : ℕ}
    (g : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (g.map φ) (fun j => φ (u j)) = (specFirst g u).map φ := by
  unfold specFirst
  rw [map_bind₁]
  congr 2
  funext ij
  rcases ij with ⟨i, j⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [specFirstVar]
  · simp [specFirstVar]
end GroundTheory.Heights₂.Heights.Vertical
