-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.dS_conj_N_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:29.78016+00:00
-- url     : https://prove2.me/submissions/95e981e2-3fb5-45f4-a9c7-2722a020ebc5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ExistsModularFunction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_NonstandardUnimodularLattice
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_N
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_inv_eq
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_mul_dS_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
namespace PI.NUnimodLoc.UnitaryGroupMassFormula
theorem _root_.solution {k r : ℕ} {s : ℝ} (hs : s ≠ 0)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    dS k r s * g * (dS k r s)⁻¹ ∈ Nset k r ↔ g ∈ Nset k r := by
  constructor
  · intro h
    rw [dS_inv_eq hs] at h
    have h2 := dS_conj_N (inv_ne_zero hs) h
    rw [inv_inv] at h2
    have h1' := dS_mul_dS_inv (k := k) (r := r) (inv_ne_zero hs)
    rw [inv_inv] at h1'
    have e : dS k r s⁻¹ * (dS k r s * g * dS k r s⁻¹) * dS k r s = g := by
      simp only [Matrix.mul_assoc]
      rw [h1', Matrix.mul_one, ← Matrix.mul_assoc, h1', Matrix.one_mul]
    rwa [e] at h2
  · intro h
    rw [dS_inv_eq hs]
    exact dS_conj_N hs h
end PI.NUnimodLoc.UnitaryGroupMassFormula
