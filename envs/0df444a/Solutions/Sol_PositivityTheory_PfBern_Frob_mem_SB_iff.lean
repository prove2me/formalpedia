-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.mem_SB_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:43.334152+00:00
-- url     : https://prove2.me/submissions/33d26b68-cb5c-4499-b4f9-f6dcac242ec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_PullHomeoApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution {X : Type*} [TopologicalSpace X] {f : X → ℂ} :
    f ∈ SB X ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl
end PositivityTheory.PfBern.Frob
