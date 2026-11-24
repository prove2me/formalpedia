-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointLine_coeff_pairing_f4de1af45484
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:45.760728+00:00
-- url     : https://prove2.me/submissions/6b87338b-63e7-43ba-af4a-02f1f171079c

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
theorem _root_.solution (y : Fin n → ℂ) (j : Fin n) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (pairing y) = y j := by
  classical
  simp [pairing, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff]
end GroundTheory.Heights₂.Heights.PointLine
