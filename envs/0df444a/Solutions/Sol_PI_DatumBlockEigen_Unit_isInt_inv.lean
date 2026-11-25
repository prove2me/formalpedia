-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.isInt_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:50.009003+00:00
-- url     : https://prove2.me/submissions/45023f45-e701-445f-ab61-a8e114dd7190

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Theorems.Thm_PI_DatumBlockEigen_Unit_map_liftO

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
variable (O)
namespace PI.DatumBlockEigen.Unit
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n F)
    (hN : ∀ i j, N i j ∈ O) (hdi : N.det⁻¹ ∈ O) : ∀ i j, N⁻¹ i j ∈ O := by
  intro i j
  have hadj : N.adjugate = (liftO O N hN).adjugate.map O.subtype := by
    rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, map_liftO]
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, hadj, smul_eq_mul]
  exact O.mul_mem hdi ((liftO O N hN).adjugate i j).2
end PI.DatumBlockEigen.Unit
