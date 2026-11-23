-- Prove2me | solution 1 for P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_one__ef0fa3e7b004
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:54.382796+00:00
-- url     : https://prove2.me/submissions/517d8520-8f74-4bbc-aaf7-cb130b8e0786

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.NormVal
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]
namespace GlobalTheory.UnitLemma.Unr.NormVal
theorem _root_.solution : val O (1 : E) = 0 := by simp [val]
end GlobalTheory.UnitLemma.Unr.NormVal
