-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCDet_one_le_re_det_one_add_4908d4f28098
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:11.291201+00:00
-- url     : https://prove2.me/submissions/89a03799-a3ab-476c-8a7d-16fefa85a608

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCDet
open Matrix
open scoped MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
namespace GroundTheory.Heights₂.Heights.MCDet
theorem _root_.solution {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
    1 ≤ RCLike.re (1 + Q).det := by
  have hspec := hQ.isHermitian.spectral_theorem
  set U := hQ.isHermitian.eigenvectorUnitary
  have hUU : (U : Matrix n n 𝕜) * star (U : Matrix n n 𝕜) = 1 := Unitary.coe_mul_star_self U
  have h1 : 1 + Q = (U : Matrix n n 𝕜) *
      ((1 : Matrix n n 𝕜) + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)) *
        star (U : Matrix n n 𝕜) := by
    conv_lhs => rw [hspec]
    rw [Unitary.conjStarAlgAut_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU]
  have hdet : (1 + Q).det =
      ((1 : Matrix n n 𝕜) + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)).det := by
    rw [h1, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      Unitary.coe_star_mul_self, det_one, one_mul]
  rw [hdet, ← diagonal_one, diagonal_add, det_diagonal]
  have : ∏ i, ((1 : 𝕜) + (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues) i) =
      ((∏ i, (1 + hQ.isHermitian.eigenvalues i) : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [this, RCLike.ofReal_re]
  exact Finset.one_le_prod fun i _ => by linarith [hQ.eigenvalues_nonneg i]
end GroundTheory.Heights₂.Heights.MCDet
