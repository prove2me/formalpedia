-- Prove2me | solution 1 for ProbabilityTheory.klDiv_compProd_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:41.363151+00:00
-- url     : https://prove2.me/submissions/0e35f07c-b4bc-4cf2-89cf-2ba5e40c033b

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Theorems.Thm_ProbabilityTheory_rnDeriv_compProd_right

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ProbabilityTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
namespace ProbabilityTheory
theorem _root_.solution
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {μ : Measure α} {κ η : Kernel α β}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
  have h_kernel_ac : ∀ᵐ a ∂μ, κ a ≪ η a :=
    (Measure.absolutelyContinuous_compProd_right_iff).mp h_ac
  have hmeas :
      Measurable
        (fun p : α × β ↦
          ENNReal.ofReal (InformationTheory.klFun ((κ.rnDeriv η p.1 p.2).toReal))) := by
    exact
      (InformationTheory.measurable_klFun.comp
        (κ.measurable_rnDeriv η).ennreal_toReal).ennreal_ofReal
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h_ac]
  calc
    ∫⁻ p, ENNReal.ofReal
        (InformationTheory.klFun (((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal)) ∂μ ⊗ₘ η
      = ∫⁻ p,
          ENNReal.ofReal (InformationTheory.klFun ((κ.rnDeriv η p.1 p.2).toReal)) ∂μ ⊗ₘ η := by
          refine lintegral_congr_ae ?_
          exact (rnDeriv_compProd_right (μ := μ) (κ := κ) (η := η)).mono fun p hp => by
            simp [hp]
    _ = ∫⁻ a,
          ∫⁻ b, ENNReal.ofReal (InformationTheory.klFun ((κ.rnDeriv η a b).toReal)) ∂η a ∂μ := by
          rw [Measure.lintegral_compProd hmeas]
    _ = ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [h_kernel_ac] with a ha
          rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac ha]
          refine lintegral_congr_ae ?_
          exact (κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)).mono fun x hx => by
            simp [hx]
end ProbabilityTheory
