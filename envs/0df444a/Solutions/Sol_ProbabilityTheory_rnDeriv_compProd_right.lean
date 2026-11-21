-- Prove2me | solution 1 for ProbabilityTheory.rnDeriv_compProd_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:53.671403+00:00
-- url     : https://prove2.me/submissions/fb2df47f-7f16-411f-9dca-0686d3fb460d

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler

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
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ κ.rnDeriv η p.1 p.2 := by
  have hs : μ ⊗ₘ κ.singularPart η ⟂ₘ μ ⊗ₘ η :=
    MeasureTheory.Measure.MutuallySingular.compProd_of_right _ _
      (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  have hadd :
      μ ⊗ₘ κ = μ ⊗ₘ κ.singularPart η
        + (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2) := by
    calc
      μ ⊗ₘ κ
        = μ ⊗ₘ (Kernel.withDensity η (Kernel.rnDeriv κ η) + Kernel.singularPart κ η) := by
            rw [Kernel.rnDeriv_add_singularPart]
      _ = μ ⊗ₘ Kernel.withDensity η (Kernel.rnDeriv κ η) + μ ⊗ₘ Kernel.singularPart κ η := by
            rw [Measure.compProd_add_right]
      _ = (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2)
          + μ ⊗ₘ Kernel.singularPart κ η := by
            rw [Measure.compProd_withDensity]
            exact κ.measurable_rnDeriv η
      _ = μ ⊗ₘ Kernel.singularPart κ η
          + (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2) := by
            rw [add_comm]
  exact (Measure.eq_rnDeriv (κ.measurable_rnDeriv η) hs hadd).symm
end ProbabilityTheory
