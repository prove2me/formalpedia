-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum.unf_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:40.253089+00:00
-- url     : https://prove2.me/submissions/b0f8440a-7e58-4437-9849-1614f9543af4

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_IsFirstChernFamily
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_MeasurableSh
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_UnfoldingIntegralSum_measurable_sh
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_UnfoldingIntegralSum_unf_lint

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
open scoped ENNReal
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
variable {V A : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
namespace PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
theorem _root_.solution {Γ : AddSubgroup V} {Δ : AddSubgroup A} [Countable Γ] [Countable Δ]
    {ν : Measure V} [ν.IsAddHaarMeasure] {lam : Measure A} [lam.IsAddHaarMeasure]
    {𝓤 : Set V} (hU : IsAddFundamentalDomain Γ 𝓤 ν) (hU1 : ν 𝓤 = 1)
    (hUU : IsAddFundamentalDomain (Γ.prod Γ) (𝓤 ×ˢ 𝓤) (ν.prod ν))
    {𝓐 : Set A} (hA : IsAddFundamentalDomain Δ 𝓐 lam)
    (Λ : (V × V) ≃ₜ+ (V × V)) (hΛ : ∀ w, w ∈ Γ.prod Γ ↔ Λ w ∈ Γ.prod Γ)
    {Q : V × V → A} (hQ : Measurable Q) {Z : V → V → A} (hZ : Measurable (Function.uncurry Z)) :
    Measure.sum (fun c : Γ × Δ => ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod (lam.restrict 𝓐))).map
      (sh Λ Q Z ((c.1 : V), (c.2 : A)))) = ν.prod lam := by
  ext S hS
  have hsh : ∀ c : V × A, Measurable (sh Λ Q Z c) := fun c => measurable_sh hQ hZ c
  have h := unf_lint hU hU1 hUU hA Λ hΛ hQ hZ (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS] at h
  rw [Measure.sum_apply _ hS, ← h, lintegral_tsum (f := fun (c : Γ × Δ) (p : V × (V × A)) =>
    S.indicator 1 (sh Λ Q Z ((c.1 : V), (c.2 : A)) p)) fun c =>
    ((measurable_one.indicator hS).comp (hsh _)).aemeasurable]
  refine tsum_congr fun c => ?_
  rw [Measure.map_apply (hsh _) hS, ← lintegral_indicator_one (hsh _ hS)]
  rfl
end PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
