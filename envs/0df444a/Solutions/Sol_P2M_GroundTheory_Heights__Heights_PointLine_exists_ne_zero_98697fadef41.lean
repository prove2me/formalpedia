-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointLine_exists_ne_zero_98697fadef41
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:00.168514+00:00
-- url     : https://prove2.me/submissions/3d5ad15b-2ae8-40b3-b042-1ae5e9472c48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine

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
open GroundTheory.Heights₂.Heights.PointLine
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointLine
theorem _root_.solution {y : Fin n → ℂ} (hy : y ≠ 0) : ∃ a, y a ≠ 0 := by
  by_contra h
  push Not at h
  exact hy (funext h)
end GroundTheory.Heights₂.Heights.PointLine
