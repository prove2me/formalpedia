-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:55:48.608838+00:00
-- url     : https://prove2.me/submissions/6c784716-dc6f-4d3c-af71-165ab528be33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_gm_spec
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (γ : I.GFset) (v : InfinitePlace I.F) :
    Formalism.MainNotions.S.uMat ((x⁻¹ * (γ : I.GA) * y).1 v) = amat I x y v (gm I γ) := by
  obtain ⟨h1, -⟩ := gm_spec I γ
  rw [amat, ← h1 v]
  simp only [Formalism.MainNotions.S.uMat, Prod.fst_mul, Prod.fst_inv, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul,
    Units.val_mul]
end PI.UnitaryGroupMassFormula.LCG
