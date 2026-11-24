-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.spl_det_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:15:09.707048+00:00
-- url     : https://prove2.me/submissions/a4f1bce5-73bf-4997-a807-564235672b2b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : IsUnit (I.J.map (inclV I v)).det := by
  have h := RingHom.map_det (inclV I v) I.J
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact (isUnit_iff_ne_zero.2 I.J_det).map _
end PI.UnitaryGroupMassFormula.AdIndexEq
