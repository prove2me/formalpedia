-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Specmeas.ofR_eq_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:37.431083+00:00
-- url     : https://prove2.me/submissions/a37ac7f9-41e5-42c9-b8a1-652b1eaee5e7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Specmeas
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_im_ofR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P PositivityTheory.Rg.BcB.E2.P.Specmeas
variable {X : Type} [TopologicalSpace X]
variable (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f))
include hΛ
namespace PositivityTheory.Rg.BcB.E2.P.Specmeas
theorem _root_.solution (g : C(X, ℝ)) : Λ (ofR g) = ((Λ (ofR g)).re : ℂ) := by
  apply Complex.ext <;> simp [im_ofR Λ hΛ g]
end PositivityTheory.Rg.BcB.E2.P.Specmeas
