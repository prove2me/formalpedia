-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.mem_eqv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:49.643086+00:00
-- url     : https://prove2.me/submissions/c6ca6a32-f186-489c-8cef-f4d5c25fbf98

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
variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X] [ContinuousConstSMul G X]
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution {χ : G →* ℂˣ} {D : Distr X} :
    D ∈ eqv X χ ↔ ∀ (g : G) (f : SB X), D (transl g f) = (χ g : ℂ) * D f :=
  Iff.rfl
end PositivityTheory.PfBern.Frob
