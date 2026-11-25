-- Prove2me | solution 1 for PI.GTS.re_normFock_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:18.157556+00:00
-- url     : https://prove2.me/submissions/6e1a3082-c1ef-4386-b69a-68999ed76c38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
import Theorems.Thm_PI_GTS_fockF_smul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTS
open Formalism.BasicNotions MvPolynomial
namespace PI.GTS
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (c : ℂ) (x : MvPolynomial (Fin N × Fin N) ℂ) :
    (normFock lam (c • x) (c • x)).re = ‖c‖ ^ 2 * (normFock lam x x).re := by
  unfold normFock
  rw [fockF_smul_self, mul_div_assoc]
  have hc : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [show star c = (starRingEnd ℂ) c from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hc, Complex.re_ofReal_mul]
end PI.GTS
