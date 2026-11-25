-- Prove2me | solution 1 for PI.VolStabW.muInvInf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:03.613192+00:00
-- url     : https://prove2.me/submissions/005713c2-1893-45f1-a108-b134efa9600e

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
theorem _root_.solution (hU : SdUniq) : MuInvInf := by
  unfold MuInvInf
  unfold SdUniq at hU
  unfold InCtx at hU ⊢
  intro F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 ψ hψ μ hμ h
  exact ((@hU F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) ψ hψ).1 _ _
    (TopoMuInv.selfDual_map (Ainf F) _ _ (psiInf F ψ) μ hμ h) hμ
end PI.VolStabW
