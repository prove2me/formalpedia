-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScalDeg.gv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:28.389332+00:00
-- url     : https://prove2.me/submissions/eded670b-0cce-4a84-ab23-a5e23f24b3b4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScalDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScalDeg
open MvPolynomial PI.ScalDeg
namespace PI.UnitaryGroupMassFormula.ScalDeg
theorem _root_.solution {T : Type} {N N' : ℕ} (s s' : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ)
    (k : FrV T N) : gv (fun τ => s τ * s' τ) y' k = C (s k.1) * gv s' y' k := by
  unfold gv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_assoc, ← C_mul, mul_assoc]
end PI.UnitaryGroupMassFormula.ScalDeg
