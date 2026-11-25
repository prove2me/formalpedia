-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_delta_factor_eq_det_6686b3b8ba3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:21.127861+00:00
-- url     : https://prove2.me/submissions/7c687fd1-dca7-41cf-a206-56a3688789c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {T : Type} [Fintype T] [DecidableEq T] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution (τ : T) :
    ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b) : MvPolynomial (T × Fin N) ℝ) =
      (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))).det := by
  rw [Matrix.det_vandermonde]
  simp only [neg_sub_neg]
end GroundTheory.Heights₂.Heights.AntisymDivisible
