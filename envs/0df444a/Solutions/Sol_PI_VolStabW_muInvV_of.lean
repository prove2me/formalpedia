-- Prove2me | solution 1 for PI.VolStabW.muInvV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:21.480164+00:00
-- url     : https://prove2.me/submissions/942234f9-f92a-4d47-b940-b8fac16f833b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMuInv
import Theorems.Thm_PI_VolStabW_TopoMuInv_selfDual_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (hU : SdUniq) : MuInvV := by
  unfold MuInvV
  unfold SdUniq at hU
  unfold InCtx at hU ⊢
  intro F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 ψ hψ v μ hμ h
  exact ((((@hU F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) ψ hψ).2.2 v).1 _ _
    (TopoMuInv.selfDual_map (Fv F v) _ _ (psiV F ψ v) μ hμ h) hμ)
end PI.VolStabW
