-- Prove2me | solution 1 for ProbabilityTheory.condDistrib_eq_prod_of_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:45:22.625102+00:00
-- url     : https://prove2.me/submissions/9d8cc8fe-30e2-43a5-888b-f1b4cdb4802b

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_ProbabilityTheory_condDistrib_apply
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
variable {V : Type*} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
  {W : Ω → V}
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution [Nonempty S]
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IndepFun (fun ω ↦ (X ω, Z ω)) (fun ω ↦ (Y ω, W ω)) μ) :
    condDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (Z ω, W ω)) μ
      =ᵐ[μ.map (fun ω ↦ (Z ω, W ω))] Kernel.prodMkRight V (condDistrib X Z μ)
        ×ₖ Kernel.prodMkLeft U (condDistrib Y W μ) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply (hZ.prodMk hW) (.singleton _)] at hx
  ext s hs
  rw [condDistrib_apply (hX.prodMk hY) (hZ.prodMk hW) _ _ hx, Kernel.prod_apply' _ _ _ hs]
  simp_rw [Kernel.prodMkLeft_apply, Kernel.prodMkRight_apply]
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod] at hx
  have hxZ : μ (Z ⁻¹' {x.1}) ≠ 0 := fun h0 ↦ hx (measure_mono_null Set.inter_subset_left h0)
  have hxW : μ (W ⁻¹' {x.2}) ≠ 0 :=
    fun h0 ↦ hx (measure_mono_null Set.inter_subset_right h0)
  simp_rw [lintegral_eq_tsum, condDistrib_apply hX hZ μ _ hxZ,
    condDistrib_apply hY hW μ _ hxW, Measure.map_apply (hX.prodMk hY) hs]
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod,
    cond_apply ((hZ (.singleton _)).inter (hW (.singleton _)))]
  simp_rw [Measure.map_apply hX (.singleton _),
    cond_apply (hZ (.singleton _))]
  change (μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2}))⁻¹
      * μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2} ∩ (fun a ↦ (X a, Y a)) ⁻¹' s)
    = ∑' x_1, (μ (Z ⁻¹' {x.1}))⁻¹ * μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x_1})
      * ((μ[|W ⁻¹' {x.2}]).map Y) (Prod.mk x_1 ⁻¹' s)
  simp_rw [Measure.map_apply hY (measurable_prodMk_left hs),
    cond_apply (hW (.singleton _))]
  have hZW : IndepFun Z W μ := by
    have h' := IndepFun.comp h measurable_snd measurable_snd
    exact h'
  have h_indep1 : (μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2}))⁻¹
      = (μ (Z ⁻¹' {x.1}))⁻¹ * (μ (W ⁻¹' {x.2}))⁻¹ := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul.mp hZW _ _ (.singleton _)
      (.singleton _), ENNReal.mul_inv (Or.inl hxZ) (Or.inl (measure_ne_top _ _))]
  rw [h_indep1]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]
  congr 1
  simp_rw [← mul_assoc, mul_comm _ (μ (W ⁻¹' {x.2}))⁻¹, mul_assoc, ENNReal.tsum_mul_left]
  congr 1
  have h_Union : (fun ω ↦ (X ω, Y ω)) ⁻¹' s = ⋃ a,
    ((X ⁻¹' {a}) ∩ (Y ⁻¹' (Prod.mk a ⁻¹' s))) := by
    ext1; simp
  rw [h_Union, Set.inter_iUnion, measure_iUnion]
  rotate_left
  · intro i j hij
    rw [Function.onFun, Set.disjoint_iff]
    intro y
    simp_all
  · intro b
    refine ((hZ (.singleton _)).inter (hW (.singleton _))).inter ?_
    exact (hX (.singleton _)).inter (hY (measurable_prodMk_left hs))
  congr with b
  calc μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2} ∩ (X ⁻¹' {b} ∩ Y ⁻¹' (Prod.mk b ⁻¹' s)))
    = μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {b} ∩
        (W ⁻¹' {x.2} ∩ Y ⁻¹' (Prod.mk b ⁻¹' s))) := by
        rw [Set.inter_assoc, ← Set.inter_assoc (W ⁻¹' {x.2}), Set.inter_comm (W ⁻¹' {x.2}),
          ← Set.inter_assoc, ← Set.inter_assoc, ← Set.inter_assoc]
  _ = μ ((fun ω ↦ (X ω, Z ω)) ⁻¹' {(b, x.1)}
      ∩ ((fun ω ↦ (Y ω, W ω)) ⁻¹' ((Prod.mk b ⁻¹' s) ×ˢ {x.2}))) := by
        rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod, Set.inter_comm (Z ⁻¹' {x.1}),
          Set.mk_preimage_prod, Set.inter_comm (W ⁻¹' {x.2})]
  _ = μ ((fun ω ↦ (X ω, Z ω)) ⁻¹' {(b, x.1)})
      * μ ((fun ω ↦ (Y ω, W ω)) ⁻¹' ((Prod.mk b ⁻¹' s) ×ˢ {x.2})) := by
        refine indepFun_iff_measure_inter_preimage_eq_mul.mp h _ _ (.singleton _) ?_
        exact (measurable_prodMk_left hs).prod (.singleton _)
  _ = μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {b}) *
      μ (W ⁻¹' {x.2} ∩ Y ⁻¹' (Prod.mk b ⁻¹' s)) := by
        rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod, Set.inter_comm (Z ⁻¹' {x.1}),
          Set.mk_preimage_prod, Set.inter_comm (W ⁻¹' {x.2})]
end _root_.ProbabilityTheory
end ProbabilityTheory
