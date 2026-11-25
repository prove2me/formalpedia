-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:45.874436+00:00
-- url     : https://prove2.me/submissions/87abb3d4-8f59-4638-8f70-4c5e89eead9f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhConvProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhConvProj PI.UnitaryGroupMassFormula.PhConvProj.Defs
open PI.PhConvProj
namespace PI.UnitaryGroupMassFormula.PhConvProj.Defs
theorem _root_.solution (h1 : SelfAdjStep) (h2 : SandStep) : ConvProj := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m hph hci K _ _ π T hπ hT
  have hsa := h1 G μ ph m hph hci K π T hπ hT
  have hsw := h2 G μ ph m hph hci K π T hπ hT
  obtain ⟨hπ1, -⟩ := hπ
  obtain ⟨hm1, -⟩ := hci
  refine ⟨hsa, ?_, hsw⟩
  have h := hsw 1
  rw [hπ1, hm1, one_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] at h
  exact h
end PI.UnitaryGroupMassFormula.PhConvProj.Defs
