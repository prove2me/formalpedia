-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum.unf_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:20.634931+00:00
-- url     : https://prove2.me/submissions/35c6aa01-0af2-4e94-b039-6337fd1871d0

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_IsFirstChernFamily
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_MeasurableSh
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_UnfoldingIntegralSum_measurable_sh
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_UnfoldingIntegralSum_unf_lint
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_UnfoldingIntegralSum_unf_sum

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
    {Q : V × V → A} (hQ : Measurable Q) {Z : V → V → A} (hZ : Measurable (Function.uncurry Z))
    {g : V × A → ℂ} (hg : Measurable g) (hfin : ∫⁻ c, ‖g c‖ₑ ∂(ν.prod lam) < ⊤) :
    ∫ p, ∑' c : Γ × Δ, g (sh Λ Q Z ((c.1 : V), (c.2 : A)) p)
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod (lam.restrict 𝓐))) =
      ∫ c, g c ∂(ν.prod lam) := by
  have hsh : ∀ c : V × A, Measurable (sh Λ Q Z c) := fun c => measurable_sh hQ hZ c
  have hsum := unf_sum hU hU1 hUU hA Λ hΛ hQ hZ
  have hlin := unf_lint hU hU1 hUU hA Λ hΛ hQ hZ hg.enorm
  have hf' : ∑' c : Γ × Δ, ∫⁻ p, ‖g (sh Λ Q Z ((c.1 : V), (c.2 : A)) p)‖ₑ
      ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod (lam.restrict 𝓐))) ≠ ⊤ := by
    rw [← lintegral_tsum (f := fun (c : Γ × Δ) (p : V × (V × A)) =>
      ‖g (sh Λ Q Z ((c.1 : V), (c.2 : A)) p)‖ₑ) fun c => (hg.comp (hsh _)).enorm.aemeasurable, hlin]
    exact hfin.ne
  rw [integral_tsum (f := fun (c : Γ × Δ) (p : V × (V × A)) => g (sh Λ Q Z ((c.1 : V), (c.2 : A)) p))
    (fun c => (hg.comp (hsh _)).aestronglyMeasurable) hf']
  have hI : Integrable g (ν.prod lam) := ⟨hg.aestronglyMeasurable, hfin⟩
  rw [← hsum] at hI ⊢
  rw [integral_sum_measure hI]
  refine tsum_congr fun c => ?_
  rw [integral_map (hsh _).aemeasurable hg.aestronglyMeasurable]
end PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
