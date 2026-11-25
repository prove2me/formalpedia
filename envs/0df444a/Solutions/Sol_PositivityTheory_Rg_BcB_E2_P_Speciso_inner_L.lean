-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Speciso.inner_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:46.785801+00:00
-- url     : https://prove2.me/submissions/0ea0cd0a-03e6-4a66-ba12-08469c18be52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Speciso

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
    inner ℂ (π f v) (π f v) =
      inner ℂ (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : inner ℂ (π f v) (π f v) = ∫ s, (star f * f) s ∂ν := by
    rw [hν, map_mul, map_star, ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  rw [h1]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := ν) f] with s hs
  rw [hs]
  simp [Complex.conj_mul']
end PositivityTheory.Rg.BcB.E2.P.Speciso
