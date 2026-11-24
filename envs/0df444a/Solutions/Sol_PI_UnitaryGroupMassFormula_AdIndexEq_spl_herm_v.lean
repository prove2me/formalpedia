-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.spl_herm_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:22.899871+00:00
-- url     : https://prove2.me/submissions/19d3116c-2a81-4b9b-8aee-7dd1a6f07c38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_sigV_inclV
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.UG.cT (sigV I v) (I.J.map (inclV I v)) = I.J.map (inclV I v) := by
  have h := I.J_herm
  unfold Formalism.UG.IsHerm at h
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij ⊢
  rw [spl_sigV_inclV, hij]
end PI.UnitaryGroupMassFormula.AdIndexEq
