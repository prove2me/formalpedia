-- Prove2me | solution 1 for PI.OmFibreUniq.W.fib_compactOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:43.040569+00:00
-- url     : https://prove2.me/submissions/6f587856-7e56-4576-aaec-dc0b348e5796

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_UniqGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W
open MeasureTheory Topology Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
variable {V X Y : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [TotallyDisconnectedSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]
namespace PI.OmFibreUniq.W
theorem _root_.solution {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
    {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν Set.univ fib) {K : Set V}
    (hKc : IsCompact K) (hKo : IsOpen K) (hKU : K ⊆ U) :
    (∀ b, fib b K < ∞) ∧ Continuous (fun b => (fib b K).toReal) := by
  have hKcl : IsClopen K := ⟨hKc.isClosed, hKo⟩
  have hKm : MeasurableSet K := hKo.measurableSet
  have hcont : Continuous (K.indicator (1 : V → ℝ)) := hKcl.continuous_indicator continuous_const
  have hcs : HasCompactSupport (K.indicator (1 : V → ℝ)) :=
    HasCompactSupport.intro hKc fun x hx => by simp [hx]
  have hts : tsupport (K.indicator (1 : V → ℝ)) ⊆ U :=
    (closure_minimal (support_indicator_subset) hKcl.1).trans hKU
  obtain ⟨hint, hco⟩ := h.2.2 _ hcont hcs hts
  have hEq : (fun b => ∫ v, K.indicator (1 : V → ℝ) v ∂(fib b)) = fun b => (fib b K).toReal := by
    funext b
    rw [integral_indicator_one hKm]
    rfl
  refine ⟨fun b => ?_, ?_⟩
  · have hfi := (hint b (mem_univ b)).2
    have hl : ∫⁻ x, ‖K.indicator (1 : V → ℝ) x‖ₑ ∂(fib b) = fib b K := by
      rw [← lintegral_indicator_one hKm]
      congr 1
      funext x
      by_cases hx : x ∈ K <;> simp [hx]
    rw [← hl]
    exact hfi
  · rw [← hEq]
    exact continuousOn_univ.1 hco
end PI.OmFibreUniq.W
