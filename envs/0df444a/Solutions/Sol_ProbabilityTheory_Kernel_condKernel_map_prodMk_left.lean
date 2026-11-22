-- Prove2me | solution 1 for ProbabilityTheory.Kernel.condKernel_map_prodMk_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:51.382147+00:00
-- url     : https://prove2.me/submissions/5437d731-8e90-4435-9924-82dcd9eccdd1

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_P2M_ProbabilityTheory_Kernel_condKernel_apply__e1c6db4f1898
public import Theorems.Thm_MeasureTheory_lintegral_eq_tsum


set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]
open ProbabilityTheory.Kernel
variable [Countable U] [Nonempty U] [DiscreteMeasurableSpace U]
variable [Countable T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
namespace ProbabilityTheory.Kernel
theorem _root_.solution {V : Type*} [Nonempty V] [MeasurableSpace V]
    [DiscreteMeasurableSpace V] [Countable V]
    (κ : Kernel T (S × U)) [IsMarkovKernel κ] (μ : Measure T)
    (f : S × U → V) :
    condKernel (map κ (fun p ↦ (p.1, f p)))
      =ᵐ[μ ⊗ₘ fst κ] snd ((condKernel κ) ⊗ₖ (deterministic (fun x :
        (T × S) × U ↦ f (x.1.2, x.2))
          .of_discrete)) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.compProd_apply (.singleton _), lintegral_eq_tsum] at hx
  simp only [ne_eq, ENNReal.summable.tsum_eq_zero_iff, mul_eq_zero, not_forall, not_or,
    fst_apply' _ _ (measurable_prodMk_left (.singleton _)), Set.mem_preimage, Set.mem_singleton_iff]
    at hx
  obtain ⟨y, hy⟩ := hx
  have hyx1 : y = x.1 := by
    by_contra hy_ne
    refine hy.2 ?_
    rw [← Prod.eta x]
    simp_rw [Prod.mk_inj]
    simp [hy_ne]
  rw [hyx1] at hy
  ext s hs
  rw [snd_apply' _ _ hs, compProd_deterministic_apply _ (measurable_snd hs)]
  have h_ne_zero : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0 := by
    refine fun h_zero ↦ hy.2 ?_
    refine measure_mono_null ?_ h_zero
    intro p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    conv_lhs => rw [← Prod.eta x, Prod.mk_inj]
    exact fun h ↦ h.2
  have h_preimage : (fun p ↦ (p.1,
    f p)) ⁻¹' (Prod.fst ⁻¹' {x.2}) = Prod.fst ⁻¹' {x.2} := by
    ext p; simp
  rw [condKernel_apply' _ _ _, condKernel_apply' _ _ h_ne_zero]; swap
  · rw [map_apply' _ .of_discrete _ (measurable_fst (.singleton _)),
      h_preimage]
    exact h_ne_zero
  rw [map_apply' _ .of_discrete _ (measurable_fst (.singleton _)), h_preimage]
  congr
  rw [map_apply' _ .of_discrete _ ((measurableSet_singleton _).prod hs)]
  congr
  ext p
  simp only [Set.singleton_prod, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
    exists_eq_right_right, Set.mem_ofPred_eq]
  refine ⟨fun h ↦ ⟨p.2, ?_, ?_⟩, fun ⟨p2, h_mem, h_eq⟩ ↦ ?_⟩
  · simp_all
  · rw [h.2, Prod.mk.eta]
  · rw [← h_eq]
    simp [h_mem]
end ProbabilityTheory.Kernel
