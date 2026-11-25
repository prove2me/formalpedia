-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScalDeg.part_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:51:02.951751+00:00
-- url     : https://prove2.me/submissions/1f83e179-852f-454e-b1d1-601cf80e95f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScalDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScalDeg_polD_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScalDeg_gv_mul

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
theorem _root_.solution {T : Type} {N N' : ℕ} (s s' : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) :
    sclP s (polD s' Q y') = polD (fun τ => s τ * s' τ) Q y' := by
  rw [polD_eq, polD_eq]
  unfold sclP
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext k
  rw [gv_mul]
  unfold gv
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, aeval_C, aeval_X, algebraMap_eq]
  ring
end PI.UnitaryGroupMassFormula.ScalDeg
