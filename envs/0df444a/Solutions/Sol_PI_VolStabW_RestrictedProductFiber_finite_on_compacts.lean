-- Prove2me | solution 1 for PI.VolStabW.RestrictedProductFiber.finite_on_compacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:27.406965+00:00
-- url     : https://prove2.me/submissions/6bfca03c-5d5a-4843-9861-84d9afe2a866

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FiniteOnCompacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct
open PI.VolStabW.RestrictedProductFiber
namespace PI.VolStabW.RestrictedProductFiber
theorem _root_.solution {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (U : Set V) (hU : IsOpen U)
    (ν : Measure X) (B : Set X) (fib : X → Measure V) (h : IsFibreFamily μ f ι U ν B fib)
    (b : X) (hb : b ∈ B) (hC : IsClosed (f ⁻¹' {ι b})) (hCU : f ⁻¹' {ι b} ⊆ U) :
    IsFiniteMeasureOnCompacts (fib b) := by
  refine ⟨fun K hK => ?_⟩
  have hK' : IsCompact (K ∩ f ⁻¹' {ι b}) := hK.inter_right hC
  obtain ⟨φ, h1, hφc, hφU, _h01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK' hU (Set.inter_subset_right.trans hCU)
  have hint : Integrable φ (fib b) :=
    (h.2.2 φ φ.continuous hφc hφU).1 b hb
  have hnull : fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0 := h.1 b
  have hM : fib b (K ∩ f ⁻¹' {ι b}) ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib b) := by
    have hm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) (fib b) :=
      (ENNReal.continuous_ofReal.comp φ.continuous).measurable.aemeasurable
    calc fib b (K ∩ f ⁻¹' {ι b}) ≤ fib b {x | 1 ≤ ENNReal.ofReal (φ x)} := by
          refine measure_mono fun x hx => ?_
          simp only [Set.mem_ofPred_eq, h1 hx, Pi.one_apply, ENNReal.ofReal_one, le_refl]
      _ = 1 * fib b {x | 1 ≤ ENNReal.ofReal (φ x)} := (one_mul _).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib b) := mul_meas_ge_le_lintegral₀ hm 1
  calc fib b K ≤ fib b ((K ∩ f ⁻¹' {ι b}) ∪ (f ⁻¹' {ι b} ∩ U)ᶜ) := by
        refine measure_mono fun x hx => ?_
        by_cases hx2 : x ∈ f ⁻¹' {ι b} ∩ U
        · exact Or.inl ⟨hx, hx2.1⟩
        · exact Or.inr hx2
    _ ≤ fib b (K ∩ f ⁻¹' {ι b}) + fib b (f ⁻¹' {ι b} ∩ U)ᶜ := measure_union_le _ _
    _ = fib b (K ∩ f ⁻¹' {ι b}) := by rw [hnull, add_zero]
    _ < ⊤ := lt_of_le_of_lt hM hint.lintegral_lt_top
end PI.VolStabW.RestrictedProductFiber
