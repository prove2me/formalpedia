-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Weakae.inner_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:14.052844+00:00
-- url     : https://prove2.me/submissions/b16ce100-467c-44cb-b75f-ea94ccf8df3e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Weakae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open PositivityTheory.Rg.BcB.E2.P.Weakae
variable {Y S : Type} [MeasurableSpace Y] [MeasurableSpace S]
namespace PositivityTheory.Rg.BcB.E2.P.Weakae
theorem _root_.solution (ν : Measure S) [IsFiniteMeasure ν] (F : Lp ℂ 2 ν) (f : S → ℂ) (hf : f =ᵐ[ν] F)
    (A : Set S) (hA : MeasurableSet A) (hνA : ν A ≠ ⊤) :
    inner ℂ F (indicatorConstLp 2 hA hνA (1 : ℂ)) = ∫ s in A, conj (f s) ∂ν := by
  rw [← inner_conj_symm, L2.inner_indicatorConstLp_one, integral_conj]
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae (hf.mono fun s hs => hs.symm))
end PositivityTheory.Rg.BcB.E2.P.Weakae
