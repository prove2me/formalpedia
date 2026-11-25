-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.isInt_inv_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:15.55794+00:00
-- url     : https://prove2.me/submissions/b815ce9c-912a-4327-9be8-71c5ac7faa4d

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Theorems.Thm_PI_DatumBlockEigen_Unit_det_liftO
import Theorems.Thm_PI_DatumBlockEigen_Unit_unitO
import Theorems.Thm_PI_DatumBlockEigen_Unit_isInt_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Unit
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
variable {O ϖ}
namespace PI.DatumBlockEigen.Unit
theorem _root_.solution (hϖ : ϖ ∈ O) (hL : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {n : Type} [Fintype n]
    [DecidableEq n] (N : Matrix n n F) (hN : ∀ i j, N i j ∈ O)
    (hu : IsUnit (Ideal.Quotient.mk (pI O ϖ hϖ) (liftO O N hN).det)) :
    N.det ≠ 0 ∧ ∀ i j, N⁻¹ i j ∈ O := by
  obtain ⟨h0, h1⟩ := unitO hϖ hL _ hu
  rw [det_liftO] at h0 h1
  exact ⟨h0, isInt_inv O N hN h1⟩
end PI.DatumBlockEigen.Unit
