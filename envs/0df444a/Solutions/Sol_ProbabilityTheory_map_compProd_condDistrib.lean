-- Prove2me | solution 1 for ProbabilityTheory.map_compProd_condDistrib
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:18.253805+00:00
-- url     : https://prove2.me/submissions/96147cab-2ad4-4cb3-9df8-7eea6eed811f

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_P2M_ProbabilityTheory_condDistrib_apply__7130db3f8416
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
variable [MeasurableSingletonClass T]
variable [Countable U] [DiscreteMeasurableSpace U]
variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
variable [Countable T]
variable [Nonempty T]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    [Nonempty S] (hX : Measurable X) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ.map Z ⊗ₘ condDistrib X Z μ = μ.map (fun ω ↦ (Z ω, X ω)) := by
  ext A hA
  rw [Measure.map_apply (hZ.prodMk hX) hA, Measure.compProd_apply hA, lintegral_eq_tsum]
  have : ∑' x : U, μ.map Z {x} * condDistrib X Z μ x (Prod.mk x ⁻¹' A)
      = ∑' x : U, μ (Z ⁻¹' {x} ∩ (fun ω ↦ (x, X ω)) ⁻¹' A) := by
    congr 1 with x
    rw [Measure.map_apply hZ (.singleton _)]
    by_cases hx : μ (Z ⁻¹' {x}) = 0
    · simp [hx, measure_mono_null Set.inter_subset_left hx]
    rw [condDistrib_apply' hX hZ _ _ hx]
    swap; · exact (measurable_prodMk_left hA)
    rw [← mul_assoc, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_mul]
    congr
  rw [this]
  have : (fun a ↦ (Z a, X a)) ⁻¹' A = ⋃ x, Z ⁻¹' {x} ∩ ((fun a ↦ (x,
    X a)) ⁻¹' A) := by
    ext ω
    simp
  rw [this, measure_iUnion]
  · intro i j hij
    rw [Function.onFun]
    refine Disjoint.mono Set.inter_subset_left Set.inter_subset_left ?_
    rw [Set.disjoint_iff]
    intro z
    simp_all
  intro u
  exact (hZ (.singleton _)).inter (measurable_const.prodMk hX hA)
end _root_.ProbabilityTheory
end ProbabilityTheory
