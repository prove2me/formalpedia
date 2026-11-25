-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplQuadDiag_abs_det_eq_one_of_mul_transpose_83dc71c1c9f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:10.954109+00:00
-- url     : https://prove2.me/submissions/f148eed1-66bb-4dc3-a317-dfe47918e0e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplQuadDiag

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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.PSymplQuadDiag
namespace GroundTheory.Heights₂.Heights.PSymplQuadDiag
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : Matrix ι ι ℝ) (h : Oᵀ * O = 1) : |O.det| = 1 := by
  have h1 : O.det * O.det = 1 := by
    have := congrArg Matrix.det h
    rwa [det_mul, det_transpose, det_one] at this
  have h2 : |O.det| * |O.det| = 1 := by rw [← abs_mul, h1, abs_one]
  nlinarith [abs_nonneg O.det]
end GroundTheory.Heights₂.Heights.PSymplQuadDiag
