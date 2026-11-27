-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__dGam_le_example_0319b869c444
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:52.730983+00:00
-- url     : https://prove2.me/submissions/453e1f50-3d31-4b59-9b67-5b3416b326fd

import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_FmZeroHLatEmpty
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField Formalism.BasicNotions
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution {R : Ranks} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
    (C : ColumnChain R Tau hc) (h : C.DGam = 1) :
    Real.log (C.DGam : ℝ) ≤ 0 * R.f * R.N R.m * Real.log ((R.f : ℝ) * R.N R.m) := by
  rw [h]
  simp
end Formalism.BasicNotions.Examples₂
