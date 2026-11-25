-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CdHaarScale.Main.rho_finite_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:25.848863+00:00
-- url     : https://prove2.me/submissions/28fc0d3f-c786-45a0-8a9d-6b08e0da6441

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_umat_injective
import Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_rho_iterate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main
namespace PI.UnitaryGroupMassFormula.CdHaarScale.Main
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ a, (rho π hπ)^[N] a = a := by
  refine ⟨orderOf π, (orderOf_pos π).ne', fun a => ?_⟩
  have hid : ∀ i, (π.symm)^[orderOf π] i = i := by
    intro i
    rw [show π.symm = π⁻¹ from rfl, Equiv.Perm.iterate_eq_pow, inv_pow, pow_orderOf_eq_one, inv_one]
    rfl
  apply umat_injective
  ext i j
  rw [rho_iterate, hid, hid]
end PI.UnitaryGroupMassFormula.CdHaarScale.Main
