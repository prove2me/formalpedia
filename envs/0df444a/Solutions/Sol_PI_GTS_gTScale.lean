-- Prove2me | solution 1 for PI.GTS.gTScale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:14:34.793565+00:00
-- url     : https://prove2.me/submissions/be57ef1b-1161-4f6d-8799-94ae23fb88f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
import Theorems.Thm_PI_GTS_re_normFock_smul
import Theorems.Thm_PI_GTS_norm_units_zpow_sq
import Theorems.Thm_PI_GTS_sqAct_mem_delSq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.GTS
open Formalism.BasicNotions MvPolynomial
namespace PI.GTS
theorem _root_.solution : PI.GTScale := by
  intro n N h lam sg io br hio hbr a
  obtain ⟨-, -, -, -, hio5, hio6⟩ := hio
  obtain ⟨-, -, -, -, hbr5, hbr6⟩ := hbr
  have ha : ‖(a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr a.ne_zero
  have hnn : 0 ≤ ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) := zpow_nonneg (norm_nonneg _) _
  constructor
  · intro s hs
    have hk : ‖((a⁻¹ ^ degZ lam sg : ℂˣ) : ℂ)‖ ^ 2 = ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) := by
      rw [norm_units_zpow_sq, Units.val_inv_eq_inv_val, norm_inv, inv_zpow']
    rw [hio5 a⁻¹ s hs, re_normFock_smul, hk, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hio6 s hs) hnn
  · intro f hf
    have hf' := sqAct_mem_delSq N lam (lastGL ℂ N a) f hf
    have h1 := hbr6 _ hf'
    rw [hbr5 a f hf, re_normFock_smul, norm_units_zpow_sq] at h1
    calc (normFock sg (br f) (br f)).re
        = ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) * (‖(a : ℂ)‖ ^ (2 * degZ lam sg) * (normFock sg (br f) (br f)).re) := by
          rw [← mul_assoc, ← zpow_add₀ ha]; simp
      _ ≤ ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) * (brBd h lam sg ^ 2 *
            (normFock lam (sqAct ℂ N lam (lastGL ℂ N a) f) (sqAct ℂ N lam (lastGL ℂ N a) f)).re) :=
          mul_le_mul_of_nonneg_left h1 hnn
      _ = _ := by ring
end PI.GTS
