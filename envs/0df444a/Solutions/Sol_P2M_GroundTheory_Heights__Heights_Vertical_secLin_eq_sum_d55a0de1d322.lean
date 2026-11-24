-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_sum_d55a0de1d322
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:17.825212+00:00
-- url     : https://prove2.me/submissions/784ec96e-3624-4c7c-a7aa-ba21cebec51e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity

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
variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R}
    (w : Fin n → R) : secLin Q y w = ∑ j, algebraMap R (SecAlg Q y) (w j) * secCoord Q y j := by
  simp only [secLin, linForm, map_sum, map_mul]
  rfl
end GroundTheory.Heights₂.Heights.Vertical
