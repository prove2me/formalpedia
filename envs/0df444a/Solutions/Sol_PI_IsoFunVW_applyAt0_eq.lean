-- Prove2me | solution 1 for PI.IsoFunVW.applyAt0_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:53.814378+00:00
-- url     : https://prove2.me/submissions/b217607a-edbb-4eed-9515-027599bf8af8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoFunV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE
import Theorems.Thm_PI_IsoFunVW_linW_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MvPolynomial
noncomputable section
open PI PI.IsoFunVW
open PI.IsoFunV
namespace PI.IsoFunVW
theorem _root_.solution {T : Type} [Fintype T] {N N' : ℕ} (P : MvPolynomial (Idx T N N') ℂ)
    (Θ : VC T N N' → ℂ) : applyAt0 P Θ = linW (wTh Θ) P := by
  rw [linW_apply, applyAt0]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [wTh, mul_assoc]
end PI.IsoFunVW
