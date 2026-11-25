-- Prove2me | solution 1 for PI.VolStabSW.DiscreteGroups.meas_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:20:22.441913+00:00
-- url     : https://prove2.me/submissions/20cdad3f-fc2d-4f3f-a8f9-f1848398e633

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibDis
import Theorems.Thm_PI_VolStabSW_DiscreteGroups_cover
import Theorems.Thm_PI_VolStabSW_DiscreteGroups_open_case
import Theorems.Thm_PI_VolStabSW_DiscreteGroups_null_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DiscreteGroups
open MeasureTheory Topology Set Filter PI.VolStabSW PI.VolStabSW.Glue
open scoped ENNReal
variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]
variable {X Y : Type} [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}
  (hf : Continuous f) (hι : IsClosedEmbedding ι) (hr : ∀ v, f v ∈ Set.range ι) (hU : IsOpen U)
  (h0 : ∀ b, fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0) (h2 : ∀ b K, IsCompact K → K ⊆ U → fib b K < ⊤)
  (h3 : ∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fib b)) ∧
        Continuous (fun b => ∫ v, φ v ∂(fib b)) ∧
        ∀ S : Set X, IsCompact S → ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν)
include hf hι hr hU h0 h2 h3
namespace PI.VolStabSW.DiscreteGroups
theorem _root_.solution : ∀ A, MeasurableSet A → Measurable fun b => fib b A := by
  obtain ⟨W, hW, hWU⟩ := cover U hU
  have hWsub : ∀ n, W n ⊆ U := fun n => subset_closure.trans (hW n).2.2
  have hfin : ∀ b n, fib b (W n) ≠ ⊤ := fun b n =>
    (lt_of_le_of_lt (measure_mono subset_closure) (h2 b _ (hW n).2.1 (hW n).2.2)).ne
  have hP : ∀ n, ∀ A, MeasurableSet A → Measurable fun b => fib b (A ∩ W n) := by
    intro n
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => Measurable fun b => fib b (A ∩ W n)) (s := {s : Set V | IsOpen s})
      BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_ ?_ ?_
    · simp only [empty_inter, measure_empty]; exact measurable_const
    · intro t ht
      exact (open_case hf hι hr hU h0 h2 h3 (t ∩ W n) ((ht : IsOpen t).inter (hW n).1)
        (inter_subset_right.trans (hWsub n))).1
    · intro t htm IH
      have e : ∀ b, fib b (tᶜ ∩ W n) = fib b (W n) - fib b (t ∩ W n) := by
        intro b
        rw [← measure_diff inter_subset_right (htm.inter (hW n).1.measurableSet).nullMeasurableSet
          ((measure_mono inter_subset_right).trans_lt (lt_top_iff_ne_top.2 (hfin b n))).ne]
        congr 1
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_diff]
        tauto
      simp_rw [e]
      exact (open_case hf hι hr hU h0 h2 h3 (W n) (hW n).1 (hWsub n)).1.sub IH
    · intro g hd hgm IH
      have e : ∀ b, fib b ((⋃ i, g i) ∩ W n) = ∑' i, fib b (g i ∩ W n) := by
        intro b
        rw [iUnion_inter, measure_iUnion (fun i j hij => (hd hij).mono inter_subset_left
          inter_subset_left) (fun i => (hgm i).inter (hW n).1.measurableSet)]
      simp_rw [e]
      exact Measurable.ennreal_tsum IH
  intro A hA
  have hD : ∀ n, MeasurableSet (disjointed W n) :=
    MeasurableSet.disjointed fun n => (hW n).1.measurableSet
  have e : ∀ b, fib b A = ∑' n, fib b (A ∩ disjointed W n) := by
    intro b
    rw [← measure_inter_add_diff A hU.measurableSet,
      measure_mono_null (show A \ U ⊆ Uᶜ from fun x hx => hx.2) (null_compl hf hι hr hU h0 h2 h3 b),
      add_zero,
      ← hWU, ← iUnion_disjointed, inter_iUnion,
      measure_iUnion (fun i j hij => ((disjoint_disjointed W) hij).mono inter_subset_right
        inter_subset_right) (fun n => hA.inter (hD n))]
  simp_rw [e]
  refine Measurable.ennreal_tsum fun n => ?_
  have := hP n (A ∩ disjointed W n) (hA.inter (hD n))
  simpa only [inter_eq_left.2 (inter_subset_right.trans (disjointed_subset W n))] using this
end PI.VolStabSW.DiscreteGroups
