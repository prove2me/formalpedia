-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.fix_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:22.32734+00:00
-- url     : https://prove2.me/submissions/902b7f9a-fa88-4029-8d2a-04ba1c19b2da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {W : Set (Fin n → ℂ)} {g : Matrix (Fin n) (Fin n) ℂ} (hW : ∀ x ∈ W, g *ᵥ x = x) :
    ∀ x ∈ Submodule.span ℂ W, g *ᵥ x = x := by
  intro x hx
  have hle : Submodule.span ℂ W ≤ LinearMap.ker (Matrix.mulVecLin g - LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    simp [hW y hy]
  have hx' := hle hx
  simpa [sub_eq_zero] using hx'
end PI.ScMuExists.UnitaryGroupMassFormula
