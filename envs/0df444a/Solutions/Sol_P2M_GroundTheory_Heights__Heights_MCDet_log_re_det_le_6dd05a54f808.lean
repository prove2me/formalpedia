-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCDet_log_re_det_le_6dd05a54f808
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:08.663918+00:00
-- url     : https://prove2.me/submissions/977bcb2e-121a-4340-a644-82dbc9f4a037

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
theorem _root_.solution {A : Matrix n n 𝕜} (hA : A.PosDef) :
    Real.log (RCLike.re A.det) ≤ RCLike.re A.trace - Fintype.card n := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues,
    ← RCLike.ofReal_prod, ← RCLike.ofReal_sum, RCLike.ofReal_re, RCLike.ofReal_re,
    Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')]
  have : (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)
end GroundTheory.Heights₂.Heights.MCDet
