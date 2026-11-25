-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Speciso.norm_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:35.551391+00:00
-- url     : https://prove2.me/submissions/bd7b8b9c-64ce-4737-8748-46d99c988249

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Speciso
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Speciso_inner_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open PositivityTheory.Rg.BcB.E2.P.Speciso
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {S : Type}
  [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
namespace PositivityTheory.Rg.BcB.E2.P.Speciso
theorem _root_.solution (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) (ν : Measure S) [IsFiniteMeasure ν]
    (hν : ∀ f : C(S, ℂ), ∫ s, f s ∂ν = inner ℂ v (π f v)) (f : C(S, ℂ)) :
    ‖Lmap π v f‖ = ‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ f‖ := by
  have h := congrArg RCLike.re (inner_L π v ν hν f)
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
end PositivityTheory.Rg.BcB.E2.P.Speciso
