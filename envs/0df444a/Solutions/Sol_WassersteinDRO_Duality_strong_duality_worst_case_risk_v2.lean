-- Prove2me | solution 1 for WassersteinDRO.Duality.strong_duality_worst_case_risk_v2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:33:28.709137+00:00
-- url     : https://prove2.me/submissions/bbaa511b-118e-4063-91dc-8dac4f067220

import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_WassersteinDRO_Duality_moreauYosida_v2
import Definitions.Def_WassersteinDRO_Duality_nominalRisk_v2
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk_v2
import Mathlib

-- Complete local proof: Solutions.Duality_CappedChoice
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

noncomputable def selectorPenalty {E : Type*} (G C : E × E → ℝ) (γ : ℝ)
    (T : E → E) (y : E) : ℝ := G (T y,y) - γ * C (T y,y)

def selectorQuality {E : Type*} (G C : E × E → ℝ) (γ n : ℝ) (T : E → E) : Prop :=
  ∀ y, G (T y,y) ≤ n ∧ C (T y,y) ≤ n ∧ 0 ≤ selectorPenalty G C γ T y

noncomputable def cappedChoice {E : Type*} (G C : E × E → ℝ) (γ n : ℝ)
    (z y : E) : E :=
  if G (z,y) ≤ n ∧ C (z,y) ≤ n ∧ 0 ≤ G (z,y) - γ * C (z,y) then z else y

noncomputable def cappedPenalty {E : Type*} (G C : E × E → ℝ) (γ n : ℝ)
    (z y : E) : ENNReal :=
  if G (z,y) ≤ n ∧ C (z,y) ≤ n then ENNReal.ofReal (G (z,y) - γ * C (z,y)) else 0

lemma measurable_cappedChoice {E : Type*} [MeasurableSpace E]
    (G C : E × E → ℝ) (hG : Measurable G) (hC : Measurable C)
    (γ n : ℝ) (z : E) : Measurable (cappedChoice G C γ n z) := by
  have hgm : Measurable (fun y => G (z,y)) := hG.comp (measurable_const.prodMk measurable_id)
  have hcm : Measurable (fun y => C (z,y)) := hC.comp (measurable_const.prodMk measurable_id)
  unfold cappedChoice
  exact Measurable.ite ((measurableSet_le hgm measurable_const).inter
    ((measurableSet_le hcm measurable_const).inter
      (measurableSet_le measurable_const (hgm.sub (measurable_const.mul hcm)))))
    measurable_const measurable_id

lemma measurable_cappedPenalty {E : Type*} [MeasurableSpace E]
    (G C : E × E → ℝ) (hG : Measurable G) (hC : Measurable C)
    (γ n : ℝ) (z : E) : Measurable (cappedPenalty G C γ n z) := by
  have hgm : Measurable (fun y => G (z,y)) := hG.comp (measurable_const.prodMk measurable_id)
  have hcm : Measurable (fun y => C (z,y)) := hC.comp (measurable_const.prodMk measurable_id)
  unfold cappedPenalty
  exact Measurable.ite ((measurableSet_le hgm measurable_const).inter
    (measurableSet_le hcm measurable_const))
    (ENNReal.measurable_ofReal.comp (hgm.sub (measurable_const.mul hcm))) measurable_const

lemma cappedChoice_quality {E : Type*} (G C : E × E → ℝ)
    (hGdiag : ∀ y, G (y,y) = 0) (hCdiag : ∀ y, C (y,y) = 0)
    (γ n : ℝ) (hn : 0 ≤ n) (z : E) : selectorQuality G C γ n (cappedChoice G C γ n z) := by
  intro y
  change G (cappedChoice G C γ n z y,y) ≤ n ∧ C (cappedChoice G C γ n z y,y) ≤ n ∧
    0 ≤ G (cappedChoice G C γ n z y,y) - γ * C (cappedChoice G C γ n z y,y)
  by_cases h : G (z,y) ≤ n ∧ C (z,y) ≤ n ∧ 0 ≤ G (z,y) - γ * C (z,y)
  · have he : cappedChoice G C γ n z y = z := by rw [cappedChoice,if_pos h]
    rw [he]
    exact ⟨h.1,h.2.1,h.2.2⟩
  · have he : cappedChoice G C γ n z y = y := by rw [cappedChoice,if_neg h]
    rw [he]
    simp [hGdiag,hCdiag,hn]

lemma cappedChoice_penalty {E : Type*} (G C : E × E → ℝ)
    (hGdiag : ∀ y, G (y,y) = 0) (hCdiag : ∀ y, C (y,y) = 0)
    (γ n : ℝ) (z y : E) :
    ENNReal.ofReal (selectorPenalty G C γ (cappedChoice G C γ n z) y) =
      cappedPenalty G C γ n z y := by
  by_cases hg : G (z,y) ≤ n
  · by_cases hc : C (z,y) ≤ n
    · by_cases hs : 0 ≤ G (z,y) - γ * C (z,y)
      · simp [selectorPenalty,cappedChoice,cappedPenalty,hg,hc,hs]
      · simp [selectorPenalty,cappedChoice,cappedPenalty,hg,hc,hs,hGdiag,hCdiag,
          ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hs)]
    · simp [selectorPenalty,cappedChoice,cappedPenalty,hg,hc,hGdiag,hCdiag]
  · simp [selectorPenalty,cappedChoice,cappedPenalty,hg,hGdiag,hCdiag]

#print axioms measurable_cappedChoice
#print axioms measurable_cappedPenalty
#print axioms cappedChoice_quality
#print axioms cappedChoice_penalty
end DualityCodex

-- Complete local proof: Solutions.Duality_FiniteSelector
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

noncomputable def maxSelector {E : Type*} (G C : E × E → ℝ) (γ : ℝ)
    (T U : E → E) (y : E) : E :=
  if selectorPenalty G C γ T y ≤ selectorPenalty G C γ U y then U y else T y

lemma selectorPenalty_measurable {E : Type*} [MeasurableSpace E]
    (G C : E × E → ℝ) (hG : Measurable G) (hC : Measurable C)
    (γ : ℝ) (T : E → E) (hT : Measurable T) : Measurable (selectorPenalty G C γ T) :=
  (hG.comp (hT.prodMk measurable_id)).sub
    (measurable_const.mul (hC.comp (hT.prodMk measurable_id)))

lemma measurable_maxSelector {E : Type*} [MeasurableSpace E]
    (G C : E × E → ℝ) (hG : Measurable G) (hC : Measurable C)
    (γ : ℝ) (T U : E → E) (hT : Measurable T) (hU : Measurable U) :
    Measurable (maxSelector G C γ T U) := by
  unfold maxSelector
  exact Measurable.ite (measurableSet_le (selectorPenalty_measurable G C hG hC γ T hT)
    (selectorPenalty_measurable G C hG hC γ U hU)) hU hT

lemma maxSelector_quality {E : Type*} (G C : E × E → ℝ) (γ n : ℝ) (T U : E → E)
    (hT : selectorQuality G C γ n T) (hU : selectorQuality G C γ n U) :
    selectorQuality G C γ n (maxSelector G C γ T U) := by
  intro y
  change G (maxSelector G C γ T U y,y) ≤ n ∧ C (maxSelector G C γ T U y,y) ≤ n ∧
    0 ≤ G (maxSelector G C γ T U y,y) - γ * C (maxSelector G C γ T U y,y)
  by_cases h : selectorPenalty G C γ T y ≤ selectorPenalty G C γ U y
  · have hm : maxSelector G C γ T U y = U y := by rw [maxSelector,if_pos h]
    rw [hm]
    exact hU y
  · have hm : maxSelector G C γ T U y = T y := by rw [maxSelector,if_neg h]
    rw [hm]
    exact hT y

lemma maxSelector_penalty {E : Type*} (G C : E × E → ℝ) (γ : ℝ) (T U : E → E) (y : E) :
    ENNReal.ofReal (selectorPenalty G C γ (maxSelector G C γ T U) y) =
      ENNReal.ofReal (selectorPenalty G C γ T y) ⊔
        ENNReal.ofReal (selectorPenalty G C γ U y) := by
  by_cases h : selectorPenalty G C γ T y ≤ selectorPenalty G C γ U y
  · have hm : maxSelector G C γ T U y = U y := by rw [maxSelector,if_pos h]
    change ENNReal.ofReal (G (maxSelector G C γ T U y,y) - γ * C (maxSelector G C γ T U y,y)) = _
    rw [hm]
    exact (sup_of_le_right (ENNReal.ofReal_le_ofReal h)).symm
  · have hm : maxSelector G C γ T U y = T y := by rw [maxSelector,if_neg h]
    change ENNReal.ofReal (G (maxSelector G C γ T U y,y) - γ * C (maxSelector G C γ T U y,y)) = _
    rw [hm]
    exact (sup_of_le_left (ENNReal.ofReal_le_ofReal (le_of_not_ge h))).symm

lemma exists_finite_capped_selector {E I : Type*} [MeasurableSpace E]
    (G C : E × E → ℝ) (hG : Measurable G) (hC : Measurable C)
    (hGdiag : ∀ y, G (y,y) = 0) (hCdiag : ∀ y, C (y,y) = 0)
    (γ n : ℝ) (hn : 0 ≤ n) (z : I → E) (S : Finset I) :
    ∃ T : E → E, Measurable T ∧ selectorQuality G C γ n T ∧ ∀ y,
      ENNReal.ofReal (selectorPenalty G C γ T y) = ⨆ i ∈ S, cappedPenalty G C γ n (z i) y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨id,measurable_id,?_,?_⟩
    · intro y
      simp [selectorPenalty,hGdiag,hCdiag,hn]
    · intro y
      simp [selectorPenalty,hGdiag,hCdiag]
  | @insert i S hi ih =>
    obtain ⟨T,hTm,hTq,hTp⟩ := ih
    let U := cappedChoice G C γ n (z i)
    have hUm := measurable_cappedChoice G C hG hC γ n (z i)
    have hUq := cappedChoice_quality G C hGdiag hCdiag γ n hn (z i)
    refine ⟨maxSelector G C γ T U,measurable_maxSelector G C hG hC γ T U hTm hUm,
      maxSelector_quality G C γ n T U hTq hUq,?_⟩
    intro y
    rw [maxSelector_penalty,hTp,cappedChoice_penalty G C hGdiag hCdiag γ n (z i) y,
      Finset.iSup_insert,sup_comm]

#print axioms selectorPenalty_measurable
#print axioms measurable_maxSelector
#print axioms maxSelector_quality
#print axioms maxSelector_penalty
#print axioms exists_finite_capped_selector
end DualityCodex

-- Complete local proof: Solutions.Duality_CappedEnvelope
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

noncomputable def finiteCappedEnvelope {E I : Type*} (G C : E × E → ℝ) (γ : ℝ)
    (z : I → E) (k : Finset I × ℕ) (y : E) : ENNReal :=
  ⨆ i ∈ k.1, cappedPenalty G C γ (k.2 : ℝ) (z i) y

lemma cappedPenalty_le_uncapped {E : Type*} (G C : E × E → ℝ) (γ n : ℝ) (z y : E) :
    cappedPenalty G C γ n z y ≤ ENNReal.ofReal (G (z,y) - γ * C (z,y)) := by
  unfold cappedPenalty
  split_ifs <;> simp

lemma cappedPenalty_monotone_cap {E : Type*} (G C : E × E → ℝ)
    (γ n m : ℝ) (hnm : n ≤ m) (z y : E) :
    cappedPenalty G C γ n z y ≤ cappedPenalty G C γ m z y := by
  unfold cappedPenalty
  by_cases hn : G (z,y) ≤ n ∧ C (z,y) ≤ n
  · have hm : G (z,y) ≤ m ∧ C (z,y) ≤ m := ⟨hn.1.trans hnm,hn.2.trans hnm⟩
    simp only [if_pos hn,if_pos hm,le_refl]
  · simp [hn]

lemma finiteCappedEnvelope_monotone {E I : Type*} (G C : E × E → ℝ)
    (γ : ℝ) (z : I → E) (k l : Finset I × ℕ) (hS : k.1 ⊆ l.1) (hn : k.2 ≤ l.2) :
    finiteCappedEnvelope G C γ z k ≤ finiteCappedEnvelope G C γ z l := by
  intro y
  apply iSup_le
  intro i
  apply iSup_le
  intro hi
  exact le_iSup_of_le i (le_iSup_of_le (hS hi)
    (cappedPenalty_monotone_cap G C γ k.2 l.2 (by exact_mod_cast hn) (z i) y))

lemma finiteCappedEnvelope_measurable {E I : Type*} [MeasurableSpace E] [Countable I]
    (G C : E × E → ℝ) (hG : Measurable G) (hC : Measurable C)
    (γ : ℝ) (z : I → E) (k : Finset I × ℕ) : Measurable (finiteCappedEnvelope G C γ z k) := by
  apply Measurable.iSup
  intro i
  apply Measurable.iSup
  intro hi
  exact measurable_cappedPenalty G C hG hC γ k.2 (z i)

lemma finiteCappedEnvelope_directed {E I : Type*} (G C : E × E → ℝ)
    (γ : ℝ) (z : I → E) : Directed (· ≤ ·) (finiteCappedEnvelope G C γ z) := by
  classical
  intro k l
  refine ⟨(k.1 ∪ l.1,max k.2 l.2),?_,?_⟩
  · exact finiteCappedEnvelope_monotone G C γ z _ _ Finset.subset_union_left (le_max_left _ _)
  · exact finiteCappedEnvelope_monotone G C γ z _ _ Finset.subset_union_right (le_max_right _ _)

lemma iSup_finiteCappedEnvelope {E I : Type*} (G C : E × E → ℝ)
    (γ : ℝ) (z : I → E) (y : E) :
    (⨆ k : Finset I × ℕ, finiteCappedEnvelope G C γ z k y) =
      ⨆ i : I, ENNReal.ofReal (G (z i,y) - γ * C (z i,y)) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    exact (cappedPenalty_le_uncapped G C γ k.2 (z i) y).trans
      (le_iSup (fun j => ENNReal.ofReal (G (z j,y) - γ * C (z j,y))) i)
  · apply iSup_le
    intro i
    obtain ⟨n,hn⟩ := exists_nat_ge (max (G (z i,y)) (C (z i,y)))
    have hg : G (z i,y) ≤ (n : ℝ) := (le_max_left _ _).trans hn
    have hc : C (z i,y) ≤ (n : ℝ) := (le_max_right _ _).trans hn
    apply le_iSup_of_le ({i},n)
    apply le_iSup_of_le i
    apply le_iSup_of_le (Finset.mem_singleton_self i)
    simp [cappedPenalty,hg,hc]

lemma lintegral_uncapped_eq_iSup_capped {E I : Type*} [MeasurableSpace E] [Countable I]
    (P : Measure E) (G C : E × E → ℝ) (hG : Measurable G) (hC : Measurable C)
    (γ : ℝ) (z : I → E) :
    (∫⁻ y, ⨆ i : I, ENNReal.ofReal (G (z i,y) - γ * C (z i,y)) ∂P) =
      ⨆ k : Finset I × ℕ, ∫⁻ y, finiteCappedEnvelope G C γ z k y ∂P := by
  simp_rw [← iSup_finiteCappedEnvelope G C γ z]
  exact lintegral_iSup_directed_of_measurable
    (finiteCappedEnvelope_measurable G C hG hC γ z) (finiteCappedEnvelope_directed G C γ z)

#print axioms cappedPenalty_le_uncapped
#print axioms cappedPenalty_monotone_cap
#print axioms finiteCappedEnvelope_monotone
#print axioms finiteCappedEnvelope_measurable
#print axioms finiteCappedEnvelope_directed
#print axioms iSup_finiteCappedEnvelope
#print axioms lintegral_uncapped_eq_iSup_capped
end DualityCodex

-- Complete local proof: Solutions.Duality_CouplingValues

set_option autoImplicit false
namespace DualityCodex
open MeasureTheory

lemma probability_mixture {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (hπ : IsProbabilityMeasure π) (hρ : IsProbabilityMeasure ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsProbabilityMeasure (ENNReal.ofReal a • π + ENNReal.ofReal b • ρ) := by
  letI := hπ
  letI := hρ
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb, hab]
  norm_num

lemma mixture_second_marginal {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure (Z × Z)) (Q : Measure Z)
    (hπ : π.map Prod.snd = Q) (hρ : ρ.map Prod.snd = Q)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (ENNReal.ofReal a • π + ENNReal.ofReal b • ρ).map Prod.snd = Q := by
  rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
    hπ, hρ, ← add_smul, ← ENNReal.ofReal_add ha hb, hab]
  simp

lemma mixture_integral_toReal {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (f : Z → ENNReal)
    (hπ : (∫⁻ z, f z ∂π) ≠ ⊤) (hρ : (∫⁻ z, f z ∂ρ) ≠ ⊤)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫⁻ z, f z ∂(ENNReal.ofReal a • π + ENNReal.ofReal b • ρ)).toReal =
      a * (∫⁻ z, f z ∂π).toReal + b * (∫⁻ z, f z ∂ρ).toReal := by
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hπ)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hρ), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

lemma mixture_integral_ne_top {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (f : Z → ENNReal)
    (hπ : (∫⁻ z, f z ∂π) ≠ ⊤) (hρ : (∫⁻ z, f z ∂ρ) ≠ ⊤) (a b : ℝ) :
    (∫⁻ z, f z ∂(ENNReal.ofReal a • π + ENNReal.ofReal b • ρ)) ≠ ⊤ := by
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hπ, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hρ⟩

#print axioms probability_mixture
#print axioms mixture_second_marginal
#print axioms mixture_integral_toReal
#print axioms mixture_integral_ne_top
end DualityCodex

set_option autoImplicit false
namespace DualityCodex
open MeasureTheory

def couplingValueSet {Z : Type*} [MeasurableSpace Z] (Q : Measure Z)
    (f g : Z × Z → ENNReal) : Set (ℝ × ℝ) :=
  {v | ∃ π : Measure (Z × Z), IsProbabilityMeasure π ∧ π.map Prod.snd = Q ∧
    (∫⁻ z, f z ∂π) ≠ ⊤ ∧ (∫⁻ z, g z ∂π) ≠ ⊤ ∧
    v = ((∫⁻ z, f z ∂π).toReal, (∫⁻ z, g z ∂π).toReal)}

lemma couplingValueSet_convex {Z : Type*} [MeasurableSpace Z] (Q : Measure Z)
    (f g : Z × Z → ENNReal) : Convex ℝ (couplingValueSet Q f g) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨π, hπ, hπQ, hπf, hπg, rfl⟩
  rcases hy with ⟨ρ, hρ, hρQ, hρf, hρg, rfl⟩
  refine ⟨ENNReal.ofReal a • π + ENNReal.ofReal b • ρ,
    probability_mixture π ρ hπ hρ a b ha hb hab,
    mixture_second_marginal π ρ Q hπQ hρQ a b ha hb hab,
    mixture_integral_ne_top π ρ f hπf hρf a b,
    mixture_integral_ne_top π ρ g hπg hρg a b, ?_⟩
  rw [mixture_integral_toReal π ρ f hπf hρf a b ha hb,
    mixture_integral_toReal π ρ g hπg hρg a b ha hb]
  rfl

#print axioms couplingValueSet_convex
end DualityCodex

set_option autoImplicit false
namespace DualityCodex

/-- Positive-radius feasibility gives an attained nonnegative supporting multiplier. -/
lemma supporting_multiplier (C : Set (ℝ × ℝ)) (hC : Convex ℝ C)
    (δ V L : ℝ) (hδ : 0 < δ) (hbase : (0, L) ∈ C)
    (hbudget : ∀ z ∈ C, z.1 < δ → z.2 ≤ V) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ z ∈ C, z.2 ≤ V + γ * (z.1 - δ) := by
  let D : Set (ℝ × ℝ) := Set.Iio δ ×ˢ Set.Ioi V
  have hDconv : Convex ℝ D := (convex_Iio δ).prod (convex_Ioi V)
  have hDopen : IsOpen D := isOpen_Iio.prod isOpen_Ioi
  have hdisj : Disjoint D C := Set.disjoint_left.mpr (by
    intro z hzD hzC
    exact not_lt_of_ge (hbudget z hzC hzD.1) hzD.2)
  obtain ⟨f, k, hD, hCbound⟩ := geometric_hahn_banach_open hDconv hDopen hC hdisj
  let a := f (1, 0)
  let b := f (0, 1)
  have hf (x y : ℝ) : f (x, y) = a * x + b * y := by
    have he : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
    rw [he, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    dsimp [a, b]
    ring
  have ha : 0 ≤ a := by
    by_contra ha
    have han : 0 < -a := neg_pos.mpr (lt_of_not_ge ha)
    let t := (|k - (a * δ + b * (V + 1))| + 1) / (-a)
    have ht : 0 < t := div_pos (by positivity) han
    have hm : (-a) * t = |k - (a * δ + b * (V + 1))| + 1 := by
      dsimp [t]
      exact mul_div_cancel₀ _ han.ne'
    have hd := hD (δ - t, V + 1) (show (δ - t, V + 1) ∈ D from ⟨by change δ - t < δ; linarith, by change V < V + 1; linarith⟩)
    rw [hf] at hd
    nlinarith [le_abs_self (k - (a * δ + b * (V + 1)))]
  have hb : b ≤ 0 := by
    by_contra hb
    have hbp : 0 < b := lt_of_not_ge hb
    let t := (|k - (a * (δ - 1) + b * V)| + 1) / b
    have ht : 0 < t := div_pos (by positivity) hbp
    have hm : b * t = |k - (a * (δ - 1) + b * V)| + 1 := by
      dsimp [t]
      exact mul_div_cancel₀ _ hbp.ne'
    have hd := hD (δ - 1, V + t) (show (δ - 1, V + t) ∈ D from ⟨by change δ - 1 < δ; linarith, by change V < V + t; linarith⟩)
    rw [hf] at hd
    nlinarith [le_abs_self (k - (a * (δ - 1) + b * V))]
  have hbneg : b < 0 := by
    by_contra hbneg
    have hbzero : b = 0 := le_antisymm hb (le_of_not_gt hbneg)
    have hd := hD (δ / 2, V + 1) (show (δ / 2, V + 1) ∈ D from ⟨by change δ / 2 < δ; linarith, by change V < V + 1; linarith⟩)
    have hc := hCbound (0, L) hbase
    rw [hf, hbzero] at hd hc
    nlinarith
  have hboundary : a * δ + b * V ≤ k := by
    by_contra hle
    have hgap : 0 < a * δ + b * V - k := sub_pos.mpr (lt_of_not_ge hle)
    obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt hgap (a - b)
    have hd := hD (δ - ε, V + ε) (show (δ - ε, V + ε) ∈ D from ⟨by change δ - ε < δ; linarith, by change V < V + ε; linarith⟩)
    rw [hf] at hd
    nlinarith
  refine ⟨a / (-b), div_nonneg ha (neg_nonneg.mpr hb), ?_⟩
  intro z hz
  have hc := hboundary.trans (hCbound z hz)
  have hzeta : (z.1, z.2) = z := Prod.mk.eta
  rw [← hzeta, hf] at hc
  have hn : 0 < -b := neg_pos.mpr hbneg
  have he : V + a / (-b) * (z.1 - δ) = (a * (z.1 - δ) + (-b) * V) / (-b) := by
    field_simp [ne_of_lt hbneg]
    ring
  rw [he]
  apply (le_div_iff₀ hn).mpr
  nlinarith

#print axioms supporting_multiplier
end DualityCodex

-- Complete local proof: Solutions.Duality_SelectorIntegral
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma integrable_selected_component {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsFiniteMeasure P] (F : E × E → ℝ) (hF : Measurable F)
    (hF0 : ∀ z, 0 ≤ F z) (T : E → E) (hT : Measurable T) (n : ℝ)
    (hbound : ∀ y, F (T y,y) ≤ n) : Integrable (fun y => F (T y,y)) P := by
  apply (integrable_const n : Integrable (fun _ : E => n) P).mono'
    (hF.comp (hT.prodMk measurable_id)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  change ‖F (T y,y)‖ ≤ n
  rw [Real.norm_eq_abs,abs_of_nonneg (hF0 _)]
  exact hbound y

lemma selector_penalty_integral_le {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (G C : E × E → ℝ)
    (hG : Measurable G) (hC : Measurable C) (hG0 : ∀ z, 0 ≤ G z) (hC0 : ∀ z, 0 ≤ C z)
    (γ n α : ℝ) (hα : 0 ≤ α) (T : E → E) (hT : Measurable T)
    (hquality : selectorQuality G C γ n T)
    (hsupport : ∀ v ∈ couplingValueSet P (fun z => ENNReal.ofReal (C z))
      (fun z => ENNReal.ofReal (G z)), v.2 - γ * v.1 ≤ α) :
    (∫⁻ y, ENNReal.ofReal (selectorPenalty G C γ T y) ∂P) ≤ ENNReal.ofReal α := by
  let f : E → E × E := fun y => (T y,y)
  have hf : Measurable f := hT.prodMk measurable_id
  let π := P.map f
  have hπ : IsProbabilityMeasure π := P.isProbabilityMeasure_map hf.aemeasurable
  have hs : π.map Prod.snd = P := by
    dsimp [π]
    rw [Measure.map_map measurable_snd hf]
    exact Measure.map_id'
  have hgi := integrable_selected_component P G hG hG0 T hT n (fun y => (hquality y).1)
  have hci := integrable_selected_component P C hC hC0 T hT n (fun y => (hquality y).2.1)
  have hgmean : (∫⁻ z, ENNReal.ofReal (G z) ∂π) = ∫⁻ y, ENNReal.ofReal (G (T y,y)) ∂P := by
    dsimp [π]
    exact lintegral_map (f := fun z => ENNReal.ofReal (G z)) (ENNReal.measurable_ofReal.comp hG) hf
  have hcmean : (∫⁻ z, ENNReal.ofReal (C z) ∂π) = ∫⁻ y, ENNReal.ofReal (C (T y,y)) ∂P := by
    dsimp [π]
    exact lintegral_map (f := fun z => ENNReal.ofReal (C z)) (ENNReal.measurable_ofReal.comp hC) hf
  have hgf : (∫⁻ z, ENNReal.ofReal (G z) ∂π) ≠ ⊤ := by
    rw [hgmean]
    exact (lintegral_ofReal_ne_top_iff_integrable hgi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => hG0 _)).mpr hgi
  have hcf : (∫⁻ z, ENNReal.ofReal (C z) ∂π) ≠ ⊤ := by
    rw [hcmean]
    exact (lintegral_ofReal_ne_top_iff_integrable hci.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => hC0 _)).mpr hci
  have hmoment : ((∫⁻ z, ENNReal.ofReal (C z) ∂π).toReal,
      (∫⁻ z, ENNReal.ofReal (G z) ∂π).toReal) ∈
      couplingValueSet P (fun z => ENNReal.ofReal (C z)) (fun z => ENNReal.ofReal (G z)) :=
    ⟨π,hπ,hs,hcf,hgf,rfl⟩
  have hreal := hsupport _ hmoment
  have hgr : (∫⁻ z, ENNReal.ofReal (G z) ∂π).toReal = ∫ y, G (T y,y) ∂P := by
    rw [hgmean]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => hG0 _)
      hgi.aestronglyMeasurable).symm
  have hcr : (∫⁻ z, ENNReal.ofReal (C z) ∂π).toReal = ∫ y, C (T y,y) ∂P := by
    rw [hcmean]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => hC0 _)
      hci.aestronglyMeasurable).symm
  simp only at hreal
  rw [hgr,hcr] at hreal
  have hpi : Integrable (selectorPenalty G C γ T) P := hgi.sub (hci.const_mul γ)
  have hp0 : ∀ᵐ y ∂P, 0 ≤ selectorPenalty G C γ T y :=
    Filter.Eventually.of_forall fun y => (hquality y).2.2
  have hpf : (∫⁻ y, ENNReal.ofReal (selectorPenalty G C γ T y) ∂P) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hpi.aestronglyMeasurable hp0).mpr hpi
  apply (ENNReal.le_ofReal_iff_toReal_le hpf hα).mpr
  rw [← integral_eq_lintegral_of_nonneg_ae hp0 hpi.aestronglyMeasurable]
  unfold selectorPenalty
  rw [integral_sub hgi (hci.const_mul γ),integral_const_mul]
  exact hreal

lemma finite_capped_envelope_integral_le {E I : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (G C : E × E → ℝ)
    (hG : Measurable G) (hC : Measurable C) (hG0 : ∀ z, 0 ≤ G z) (hC0 : ∀ z, 0 ≤ C z)
    (hGdiag : ∀ y, G (y,y) = 0) (hCdiag : ∀ y, C (y,y) = 0)
    (γ α : ℝ) (hα : 0 ≤ α) (z : I → E)
    (hsupport : ∀ v ∈ couplingValueSet P (fun z => ENNReal.ofReal (C z))
      (fun z => ENNReal.ofReal (G z)), v.2 - γ * v.1 ≤ α) (k : Finset I × ℕ) :
    (∫⁻ y, finiteCappedEnvelope G C γ z k y ∂P) ≤ ENNReal.ofReal α := by
  obtain ⟨T,hTm,hTq,hTp⟩ := exists_finite_capped_selector G C hG hC hGdiag hCdiag
    γ k.2 (Nat.cast_nonneg k.2) z k.1
  change (∫⁻ y, ⨆ i ∈ k.1, cappedPenalty G C γ k.2 (z i) y ∂P) ≤ ENNReal.ofReal α
  simp_rw [← hTp]
  exact selector_penalty_integral_le P G C hG hC hG0 hC0 γ k.2 α hα T hTm hTq hsupport

lemma uncapped_envelope_integral_le {E I : Type*} [MeasurableSpace E] [Countable I]
    (P : Measure E) [IsProbabilityMeasure P] (G C : E × E → ℝ)
    (hG : Measurable G) (hC : Measurable C) (hG0 : ∀ z, 0 ≤ G z) (hC0 : ∀ z, 0 ≤ C z)
    (hGdiag : ∀ y, G (y,y) = 0) (hCdiag : ∀ y, C (y,y) = 0)
    (γ α : ℝ) (hα : 0 ≤ α) (z : I → E)
    (hsupport : ∀ v ∈ couplingValueSet P (fun z => ENNReal.ofReal (C z))
      (fun z => ENNReal.ofReal (G z)), v.2 - γ * v.1 ≤ α) :
    (∫⁻ y, ⨆ i : I, ENNReal.ofReal (G (z i,y) - γ * C (z i,y)) ∂P) ≤ ENNReal.ofReal α := by
  rw [lintegral_uncapped_eq_iSup_capped P G C hG hC γ z]
  exact iSup_le (finite_capped_envelope_integral_le P G C hG hC hG0 hC0 hGdiag hCdiag
    γ α hα z hsupport)

#print axioms integrable_selected_component
#print axioms selector_penalty_integral_le
#print axioms finite_capped_envelope_integral_le
#print axioms uncapped_envelope_integral_le
end DualityCodex

-- Complete local proof: Solutions.Duality_EnvelopeOrder
set_option autoImplicit false
namespace DualityCodex

lemma toENNReal_le_coe_iff {x : EReal} {a : ENNReal} :
    x.toENNReal ≤ a ↔ x ≤ (a : EReal) := by
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal_eq_max, max_le_iff]
  exact and_iff_right (EReal.coe_ennreal_nonneg a)

lemma ereal_toENNReal_iSup {I : Sort*} (f : I → EReal) :
    (⨆ i, f i).toENNReal = ⨆ i, (f i).toENNReal := by
  apply le_antisymm
  · apply toENNReal_le_coe_iff.mpr
    apply iSup_le
    intro i
    exact toENNReal_le_coe_iff.mp (le_iSup (fun i => (f i).toENNReal) i)
  · exact iSup_le fun i => EReal.toENNReal_le_toENNReal (le_iSup f i)

lemma ereal_iSup_sub_real {I : Sort*} (f : I → EReal) (b : ℝ) :
    (⨆ i, f i) - b = ⨆ i, f i - b := by
  apply le_antisymm
  · apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot b))
      (Or.inl (EReal.coe_ne_top b))).mpr
    apply iSup_le
    intro i
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot b))
      (Or.inl (EReal.coe_ne_top b))).mp (le_iSup (fun i => f i - b) i)
  · exact iSup_le fun i => EReal.sub_le_sub (le_iSup f i) le_rfl

#print axioms toENNReal_le_coe_iff
#print axioms ereal_toENNReal_iSup
#print axioms ereal_iSup_sub_real
end DualityCodex

-- Complete local proof: Solutions.Duality_MoreauEnvelope
set_option autoImplicit false
namespace DualityCodex

lemma countable_continuous_envelope {X I : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] (f : I → X → ℝ) (hf : ∀ i, Continuous (f i)) :
    ∃ T : Set I, T.Countable ∧ ∀ x,
      (⨆ i, (f i x : EReal)) = ⨆ i, ⨆ (_ : i ∈ T), (f i x : EReal) := by
  classical
  let U : I → Set (X × ℝ) := fun i => {v | v.2 < f i v.1}
  have hUopen : ∀ i, IsOpen (U i) := fun i =>
    isOpen_lt continuous_snd ((hf i).comp continuous_fst)
  obtain ⟨T, hTc, hU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUopen
  refine ⟨T, hTc, fun x => le_antisymm ?_ ?_⟩
  · apply EReal.ge_of_forall_gt_iff_ge.mp
    intro r hr
    obtain ⟨i, hi⟩ := lt_iSup_iff.mp hr
    have hmem : (x,r) ∈ ⋃ i, U i :=
      Set.mem_iUnion.mpr ⟨i, EReal.coe_lt_coe_iff.mp hi⟩
    rw [← hU] at hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨j,hjT,hj⟩ := hmem
    exact le_iSup_of_le j (le_iSup_of_le hjT
      (EReal.coe_le_coe_iff.mpr (show r ≤ f j x from hj.le)))
  · exact iSup_le fun i => iSup_le fun _ => le_iSup (fun i => (f i x : EReal)) i

#print axioms countable_continuous_envelope
end DualityCodex

namespace DualityCodex
open WassersteinDRO.Duality

lemma continuous_moreau_score {E : Type*} [NormedAddCommGroup E]
    (ℓ : E → ℝ) (p : ℝ) (hp : 0 ≤ p) (z : E) :
    Continuous (fun v : E × ℝ => ℓ z - v.2 * ‖z-v.1‖ ^ p) := by
  exact continuous_const.sub (continuous_snd.mul
    ((continuous_const.sub continuous_fst).norm.rpow_const (fun _ => Or.inr hp)))

lemma countable_moreau_envelope {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E] (Ξ : Set E) (ℓ : E → ℝ) (p : ℝ) (hp : 0 ≤ p) :
    ∃ T : Set Ξ, T.Countable ∧ ∀ (ξ : E) (γ : ℝ),
      moreauYosida Ξ ℓ p γ ξ =
        ⨆ z : Ξ, ⨆ (_ : z ∈ T), ((ℓ z - γ * ‖(z:E)-ξ‖ ^ p : ℝ) : EReal) := by
  obtain ⟨T, hTc, hrep⟩ := countable_continuous_envelope
    (fun (z : Ξ) (v : E × ℝ) => ℓ z - v.2 * ‖(z:E)-v.1‖ ^ p)
    (fun z => continuous_moreau_score ℓ p hp z)
  refine ⟨T,hTc,fun ξ γ => ?_⟩
  simpa only [iSup_subtype, moreauYosida] using hrep (ξ,γ)

lemma moreau_lowerSemicontinuous {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : E → ℝ) (p γ : ℝ) (hp : 0 ≤ p) :
    LowerSemicontinuous (moreauYosida Ξ ℓ p γ) := by
  unfold moreauYosida
  apply lowerSemicontinuous_iSup
  intro z
  apply lowerSemicontinuous_iSup
  intro hz
  apply Continuous.lowerSemicontinuous
  apply continuous_coe_real_ereal.comp
  exact (continuous_moreau_score ℓ p hp z).comp (continuous_id.prodMk continuous_const)

lemma moreau_measurable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (Ξ : Set E) (ℓ : E → ℝ) (p γ : ℝ) (hp : 0 ≤ p) :
    Measurable (moreauYosida Ξ ℓ p γ) :=
  (moreau_lowerSemicontinuous Ξ ℓ p γ hp).measurable

#print axioms continuous_moreau_score
#print axioms countable_moreau_envelope
#print axioms moreau_lowerSemicontinuous
#print axioms moreau_measurable
end DualityCodex

-- Complete local proof: Solutions.Duality_ExpectationMonotone
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma erealExpectation_mono {Z : Type*} [MeasurableSpace Z] (Q : Measure Z)
    (f g : Z → EReal) (hfg : f ≤ᵐ[Q] g) :
    erealExpectation Q f ≤ erealExpectation Q g := by
  have hpos : (∫⁻ z, (f z).toENNReal ∂Q) ≤ ∫⁻ z, (g z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal hz)
  have hneg : (∫⁻ z, (-g z).toENNReal ∂Q) ≤ ∫⁻ z, (-f z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hz))
  unfold erealExpectation
  by_cases hgtop : (∫⁻ z, (g z).toENNReal ∂Q) = ⊤
  · rw [if_pos hgtop]
    exact le_top
  · have hftop : (∫⁻ z, (f z).toENNReal ∂Q) ≠ ⊤ :=
      (lt_of_le_of_lt hpos (lt_top_iff_ne_top.mpr hgtop)).ne
    rw [if_neg hgtop, if_neg hftop]
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg)

#print axioms erealExpectation_mono
end DualityCodex

-- Complete local proof: Solutions.Duality_ExpectationMap
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma erealExpectation_congr_ae {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) (f g : Z → EReal) (hfg : f =ᵐ[Q] g) :
    erealExpectation Q f = erealExpectation Q g :=
  le_antisymm (erealExpectation_mono Q f g hfg.le)
    (erealExpectation_mono Q g f hfg.ge)

lemma erealExpectation_map {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (Q : Measure Z) (T : Z → Y) (hT : Measurable T)
    (f : Y → EReal) (hf : Measurable f) :
    erealExpectation (Q.map T) f = erealExpectation Q (fun z => f (T z)) := by
  unfold erealExpectation
  rw [lintegral_map (f := fun y => (f y).toENNReal) (measurable_ereal_toENNReal.comp hf) hT,
    lintegral_map (f := fun y => (-f y).toENNReal) (measurable_ereal_toENNReal.comp hf.neg) hT]

#print axioms erealExpectation_congr_ae
#print axioms erealExpectation_map
end DualityCodex

-- Complete local proof: Solutions.DualityReplay_SignedExpectation
set_option autoImplicit false
open MeasureTheory
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma erealExpectation_eq_integral {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (l : E → ℝ) (hl : Integrable l Q) :
    erealExpectation Q (fun x => (l x : EReal)) = (∫ x, l x ∂Q : ℝ) := by
  have hp : (∫⁻ x, ENNReal.ofReal (l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm l).trans_lt hl.2).ne
  have hn : (∫⁻ x, ENNReal.ofReal (-l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm (fun x => -l x)).trans_lt hl.neg.2).ne
  unfold erealExpectation
  rw [if_neg (show (∫⁻ x, ((l x : EReal)).toENNReal ∂Q) ≠ ⊤ from hp)]
  simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
  rw [ ← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hl]

lemma nominalRisk_eq_integral {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (l : E → ℝ) (hl : Integrable l Q) :
    nominalRisk Q l = (∫ x, l x ∂Q : ℝ) :=
  erealExpectation_eq_integral Q l hl

#print axioms erealExpectation_eq_integral
#print axioms nominalRisk_eq_integral
end DualityReplayCodex

-- Complete local proof: Solutions.Duality_GainExpectation
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma erealExpectation_add_nonnegative {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) (b g : Z → ℝ) (hb : Integrable b Q)
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) :
    erealExpectation Q (fun z => ((b z + g z : ℝ) : EReal)) =
      (∫ z, b z ∂Q : ℝ) + ((∫⁻ z, ENNReal.ofReal (g z) ∂Q : ENNReal) : EReal) := by
  by_cases hgtop : (∫⁻ z, ENNReal.ofReal (g z) ∂Q) = ⊤
  · have hptop : (∫⁻ z, ENNReal.ofReal (b z + g z) ∂Q) = ⊤ := by
      by_contra hfin
      have hbound : ∀ z, ENNReal.ofReal (g z) ≤
          ‖b z‖ₑ + ENNReal.ofReal (b z + g z) := by
        intro z
        rw [Real.enorm_eq_ofReal_abs]
        calc
          ENNReal.ofReal (g z) ≤ ENNReal.ofReal (|b z| + max (b z + g z) 0) := by
            apply ENNReal.ofReal_le_ofReal
            have := neg_abs_le (b z)
            have := le_max_left (b z + g z) 0
            linarith
          _ = ENNReal.ofReal |b z| + ENNReal.ofReal (max (b z + g z) 0) :=
            ENNReal.ofReal_add (abs_nonneg _) (le_max_right _ _)
          _ = ENNReal.ofReal |b z| + ENNReal.ofReal (b z + g z) := by simp
      have hle := lintegral_mono (μ := Q) hbound
      have hfinite : (∫⁻ z, ‖b z‖ₑ + ENNReal.ofReal (b z + g z) ∂Q) < ⊤ := by
        rw [lintegral_add_left' hb.aestronglyMeasurable.enorm]
        exact ENNReal.add_lt_top.mpr ⟨hb.2, lt_top_iff_ne_top.mpr hfin⟩
      rw [hgtop] at hle
      exact (not_lt_of_ge hle) hfinite
    unfold erealExpectation
    simp only [EReal.real_coe_toENNReal, hptop, if_true, hgtop, EReal.coe_ennreal_top,
      EReal.coe_add_top]
  · have hgi : Integrable g Q := ⟨hg.aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg0)).mpr
          (lt_top_iff_ne_top.mpr hgtop)⟩
    change erealExpectation Q (fun z => ((b + g) z : EReal)) = _
    rw [DualityReplayCodex.erealExpectation_eq_integral Q (b + g) (hb.add hgi)]
    simp only [Pi.add_apply]
    rw [integral_add hb hgi]
    rw [← EReal.coe_ennreal_toReal hgtop, ← EReal.coe_add]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgi.aestronglyMeasurable]

lemma erealExpectation_le_integral_add_gain {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) (b f : Z → ℝ) (hb : Integrable b Q)
    (hbm : Measurable b) (hfm : Measurable f) :
    erealExpectation Q (fun z => (f z : EReal)) ≤
      (∫ z, b z ∂Q : ℝ) +
        ((∫⁻ z, ENNReal.ofReal (max (f z - b z) 0) ∂Q : ENNReal) : EReal) := by
  rw [← erealExpectation_add_nonnegative Q b (fun z => max (f z - b z) 0)
    hb ((hfm.sub hbm).max measurable_const) (fun z => le_max_right _ _)]
  apply erealExpectation_mono
  apply Filter.Eventually.of_forall
  intro z
  apply EReal.coe_le_coe_iff.mpr
  have := le_max_left (f z - b z) 0
  linarith

#print axioms erealExpectation_le_integral_add_gain
#print axioms erealExpectation_add_nonnegative
end DualityCodex

-- Complete local proof: Solutions.Duality_ExtendedGain
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma erealExpectation_add_ennreal_of_finite {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) (b : Z → ℝ) (g : Z → ENNReal) (hb : Integrable b Q)
    (hg : Measurable g) (hfinite : (∫⁻ z, g z ∂Q) ≠ ⊤) :
    erealExpectation Q (fun z => (b z : EReal) + (g z : EReal)) =
      (∫ z, b z ∂Q : ℝ) + ((∫⁻ z, g z ∂Q : ENNReal) : EReal) := by
  have hae : ∀ᵐ z ∂Q, g z < ⊤ := ae_lt_top hg hfinite
  have hfunctions : (fun z => (b z : EReal) + (g z : EReal)) =ᵐ[Q]
      (fun z => ((b z + (g z).toReal : ℝ) : EReal)) := by
    filter_upwards [hae] with z hz
    rw [← EReal.coe_ennreal_toReal hz.ne, ← EReal.coe_add]
  have hlin : (∫⁻ z, ENNReal.ofReal (g z).toReal ∂Q) = ∫⁻ z, g z ∂Q := by
    apply lintegral_congr_ae
    exact hae.mono fun z hz => ENNReal.ofReal_toReal hz.ne
  rw [erealExpectation_congr_ae Q _ _ hfunctions]
  have h := erealExpectation_add_nonnegative Q b (fun z => (g z).toReal) hb
    (ENNReal.measurable_toReal.comp hg) (fun _ => ENNReal.toReal_nonneg)
  rw [hlin] at h
  exact h

#print axioms erealExpectation_add_ennreal_of_finite
end DualityCodex

namespace DualityCodex
open WassersteinDRO.Duality
lemma erealExpectation_add_ennreal {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) (b : Z → ℝ) (g : Z → ENNReal) (hb : Integrable b Q)
    (hg : Measurable g) :
    erealExpectation Q (fun z => (b z : EReal) + (g z : EReal)) =
      (∫ z, b z ∂Q : ℝ) + ((∫⁻ z, g z ∂Q : ENNReal) : EReal) := by
  by_cases htop : (∫⁻ z, g z ∂Q) = ⊤
  · have hbound : ∀ z, g z ≤ ‖b z‖ₑ + ((b z : EReal) + (g z : EReal)).toENNReal := by
      intro z
      by_cases hz : g z = ⊤
      · simp [hz]
      · have he : ((b z : EReal) + (g z : EReal)).toENNReal =
            ENNReal.ofReal (b z + (g z).toReal) := by
          rw [← EReal.coe_ennreal_toReal hz, ← EReal.coe_add, EReal.real_coe_toENNReal]
        rw [Real.enorm_eq_ofReal_abs, he]
        calc
          g z = ENNReal.ofReal (g z).toReal := (ENNReal.ofReal_toReal hz).symm
          _ ≤ ENNReal.ofReal (|b z| + max (b z + (g z).toReal) 0) := by
            apply ENNReal.ofReal_le_ofReal
            have := neg_abs_le (b z)
            have := le_max_left (b z + (g z).toReal) 0
            linarith
          _ = ENNReal.ofReal |b z| + ENNReal.ofReal (b z + (g z).toReal) := by
            rw [ENNReal.ofReal_add (abs_nonneg _) (le_max_right _ _)]
            simp
    have hptop : (∫⁻ z, ((b z : EReal) + (g z : EReal)).toENNReal ∂Q) = ⊤ := by
      by_contra hfin
      have hle := lintegral_mono (μ := Q) hbound
      have hfinite : (∫⁻ z, ‖b z‖ₑ + ((b z : EReal) + (g z : EReal)).toENNReal ∂Q) < ⊤ := by
        rw [lintegral_add_left' hb.aestronglyMeasurable.enorm]
        exact ENNReal.add_lt_top.mpr ⟨hb.2,lt_top_iff_ne_top.mpr hfin⟩
      rw [htop] at hle
      exact (not_lt_of_ge hle) hfinite
    unfold erealExpectation
    rw [if_pos hptop,htop,EReal.coe_ennreal_top,EReal.coe_add_top]
  · exact erealExpectation_add_ennreal_of_finite Q b g hb hg htop

#print axioms erealExpectation_add_ennreal
end DualityCodex

-- Complete local proof: Solutions.Duality_GainFallback
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

noncomputable def gainFallback {E : Type*} (ℓ : E → ℝ) (z : E × E) : E × E :=
  if ℓ z.2 ≤ ℓ z.1 then z else (z.2,z.2)

lemma measurable_gainFallback {E : Type*} [MeasurableSpace E] (ℓ : E → ℝ)
    (hl : Measurable ℓ) : Measurable (gainFallback ℓ) := by
  unfold gainFallback
  exact Measurable.ite (measurableSet_le (hl.comp measurable_snd) (hl.comp measurable_fst))
    measurable_id (measurable_snd.prodMk measurable_snd)

lemma gainFallback_snd {E : Type*} (ℓ : E → ℝ) (z : E × E) :
    (gainFallback ℓ z).2 = z.2 := by
  unfold gainFallback
  split_ifs <;> rfl

lemma gainFallback_gain {E : Type*} (ℓ : E → ℝ) (z : E × E) :
    ℓ (gainFallback ℓ z).1 = ℓ z.2 + max (ℓ z.1 - ℓ z.2) 0 := by
  unfold gainFallback
  split_ifs with h
  · rw [max_eq_left (sub_nonneg.mpr h)]
    simp
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    simp

lemma gainFallback_cost_le {E : Type*} [NormedAddCommGroup E]
    (ℓ : E → ℝ) (p : ℝ) (hp : 0 < p) (z : E × E) :
    ‖(gainFallback ℓ z).1 - (gainFallback ℓ z).2‖ ^ p ≤ ‖z.1-z.2‖ ^ p := by
  unfold gainFallback
  split_ifs
  · exact le_rfl
  · simp [Real.zero_rpow hp.ne', Real.rpow_nonneg (norm_nonneg _) p]

lemma gainFallback_supported {E : Type*} (ℓ : E → ℝ) (Ξ : Set E) (z : E × E)
    (h1 : z.1 ∈ Ξ) (h2 : z.2 ∈ Ξ) : (gainFallback ℓ z).1 ∈ Ξ := by
  unfold gainFallback
  split_ifs
  · exact h1
  · exact h2

lemma gainFallback_snd_marginal {E : Type*} [MeasurableSpace E]
    (ℓ : E → ℝ) (hl : Measurable ℓ) (π : Measure (E × E)) :
    (π.map (gainFallback ℓ)).map Prod.snd = π.map Prod.snd := by
  rw [Measure.map_map measurable_snd (measurable_gainFallback ℓ hl)]
  congr 1
  funext z
  exact gainFallback_snd ℓ z

#print axioms measurable_gainFallback
#print axioms gainFallback_snd
#print axioms gainFallback_gain
#print axioms gainFallback_cost_le
#print axioms gainFallback_supported
#print axioms gainFallback_snd_marginal
end DualityCodex

-- Complete local proof: Solutions.Duality_SupportFallback
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open scoped Classical

noncomputable def supportedGain {E : Type*} (Ξ : Set E) (ℓ : E → ℝ) (z : E × E) : ℝ :=
  if z.1 ∈ Ξ then max (ℓ z.1 - ℓ z.2) 0 else 0

noncomputable def supportedCost {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (p : ℝ) (z : E × E) : ℝ :=
  if z.1 ∈ Ξ then ‖z.1-z.2‖ ^ p else 0

noncomputable def supportedFallback {E : Type*} (Ξ : Set E) (ℓ : E → ℝ)
    (z : E × E) : E × E :=
  if z.1 ∈ Ξ then gainFallback ℓ z else (z.2,z.2)

lemma measurable_supportedFallback {E : Type*} [MeasurableSpace E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ) :
    Measurable (supportedFallback Ξ ℓ) := by
  unfold supportedFallback
  exact Measurable.ite (hΞ.preimage measurable_fst) (measurable_gainFallback ℓ hl)
    (measurable_snd.prodMk measurable_snd)

lemma measurable_supportedGain {E : Type*} [MeasurableSpace E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ) :
    Measurable (supportedGain Ξ ℓ) := by
  unfold supportedGain
  exact Measurable.ite (hΞ.preimage measurable_fst)
    (((hl.comp measurable_fst).sub (hl.comp measurable_snd)).max measurable_const)
    measurable_const

lemma measurable_supportedCost {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (p : ℝ) (hp : 0 ≤ p) :
    Measurable (supportedCost Ξ p) := by
  unfold supportedCost
  exact Measurable.ite (hΞ.preimage measurable_fst)
    ((continuous_fst.sub continuous_snd).norm.rpow_const (fun _ => Or.inr hp)).measurable
    measurable_const

lemma supportedGain_nonnegative {E : Type*} (Ξ : Set E) (ℓ : E → ℝ) (z : E × E) :
    0 ≤ supportedGain Ξ ℓ z := by
  unfold supportedGain
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

lemma supportedCost_nonnegative {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (p : ℝ) (z : E × E) : 0 ≤ supportedCost Ξ p z := by
  unfold supportedCost
  split_ifs
  · exact Real.rpow_nonneg (norm_nonneg _) _
  · exact le_rfl

lemma supportedFallback_snd {E : Type*} (Ξ : Set E) (ℓ : E → ℝ) (z : E × E) :
    (supportedFallback Ξ ℓ z).2 = z.2 := by
  unfold supportedFallback
  split_ifs
  · exact gainFallback_snd ℓ z
  · rfl

lemma supportedFallback_gain {E : Type*} (Ξ : Set E) (ℓ : E → ℝ) (z : E × E) :
    ℓ (supportedFallback Ξ ℓ z).1 = ℓ z.2 + supportedGain Ξ ℓ z := by
  unfold supportedFallback supportedGain
  split_ifs
  · exact gainFallback_gain ℓ z
  · simp

lemma supportedFallback_cost_le {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : E → ℝ) (p : ℝ) (hp : 0 < p) (z : E × E) :
    ‖(supportedFallback Ξ ℓ z).1-(supportedFallback Ξ ℓ z).2‖ ^ p ≤
      supportedCost Ξ p z := by
  unfold supportedFallback supportedCost
  split_ifs
  · exact gainFallback_cost_le ℓ p hp z
  · simp [Real.zero_rpow hp.ne']

lemma supportedFallback_supported {E : Type*} (Ξ : Set E) (ℓ : E → ℝ)
    (z : E × E) (h2 : z.2 ∈ Ξ) : (supportedFallback Ξ ℓ z).1 ∈ Ξ := by
  unfold supportedFallback
  split_ifs with h
  · exact gainFallback_supported ℓ Ξ z h h2
  · exact h2

#print axioms measurable_supportedFallback
#print axioms measurable_supportedGain
#print axioms measurable_supportedCost
#print axioms supportedGain_nonnegative
#print axioms supportedCost_nonnegative
#print axioms supportedFallback_snd
#print axioms supportedFallback_gain
#print axioms supportedFallback_cost_le
#print axioms supportedFallback_supported
end DualityCodex

-- Complete local proof: Solutions.Duality_MoreauGain
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

noncomputable def moreauGain {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : E → ℝ) (p γ : ℝ) (ξ : E) : ENNReal :=
  (moreauYosida Ξ ℓ p γ ξ - (ℓ ξ : EReal)).toENNReal

lemma moreauGain_measurable {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (Ξ : Set E) (ℓ : E → ℝ)
    (hl : Measurable ℓ) (p γ : ℝ) (hp : 0 ≤ p) : Measurable (moreauGain Ξ ℓ p γ) :=
  ((moreau_measurable Ξ ℓ p γ hp).sub hl.coe_real_ereal).ereal_toENNReal

lemma baseline_le_moreau {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : E → ℝ) (p γ : ℝ) (hp : 0 < p) (ξ : E) (hξ : ξ ∈ Ξ) :
    (ℓ ξ : EReal) ≤ moreauYosida Ξ ℓ p γ ξ := by
  apply le_iSup_of_le ξ
  apply le_iSup_of_le hξ
  simp [Real.zero_rpow hp.ne']

lemma moreau_eq_baseline_add_gain {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : E → ℝ) (p γ : ℝ) (hp : 0 < p) (ξ : E) (hξ : ξ ∈ Ξ) :
    moreauYosida Ξ ℓ p γ ξ = (ℓ ξ : EReal) + (moreauGain Ξ ℓ p γ ξ : EReal) := by
  have hnonneg : 0 ≤ moreauYosida Ξ ℓ p γ ξ - (ℓ ξ : EReal) :=
    (EReal.sub_nonneg (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _))).mpr
      (baseline_le_moreau Ξ ℓ p γ hp ξ hξ)
  unfold moreauGain
  rw [EReal.coe_toENNReal hnonneg, add_comm, EReal.sub_add_cancel]

lemma moreau_expectation_eq_baseline_add_gain {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (Ξ : Set E) (ℓ : E → ℝ)
    (hl : Measurable ℓ) (p γ : ℝ) (hp : 0 < p) (P : Measure E)
    (hPΞ : P Ξᶜ = 0) (hP : Integrable ℓ P) :
    erealExpectation P (moreauYosida Ξ ℓ p γ) = (∫ y, ℓ y ∂P : ℝ) +
      ((∫⁻ y, moreauGain Ξ ℓ p γ y ∂P : ENNReal) : EReal) := by
  have hae : ∀ᵐ y ∂P, y ∈ Ξ := ae_iff.mpr hPΞ
  rw [erealExpectation_congr_ae P _ _
    (hae.mono fun y hy => moreau_eq_baseline_add_gain Ξ ℓ p γ hp y hy)]
  exact erealExpectation_add_ennreal P ℓ (moreauGain Ξ ℓ p γ) hP
    (moreauGain_measurable Ξ ℓ hl p γ hp.le)

#print axioms moreauGain_measurable
#print axioms baseline_le_moreau
#print axioms moreau_eq_baseline_add_gain
#print axioms moreau_expectation_eq_baseline_add_gain
end DualityCodex

-- Complete local proof: Solutions.Duality_GainEnvelope
set_option autoImplicit false
namespace DualityCodex
open WassersteinDRO.Duality

lemma clipped_penalty_ofReal_eq (a b : ℝ) (hb : 0 ≤ b) :
    ENNReal.ofReal (max a 0 - b) = ENNReal.ofReal (a-b) := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_right ha',zero_sub,ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hb),
      ENNReal.ofReal_eq_zero.mpr (by linarith)]

lemma moreauGain_eq_score_sup {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : E → ℝ) (p γ : ℝ) (ξ : E) :
    moreauGain Ξ ℓ p γ ξ =
      ⨆ z : E, ⨆ (_ : z ∈ Ξ), ENNReal.ofReal (ℓ z - γ * ‖z-ξ‖ ^ p - ℓ ξ) := by
  unfold moreauGain moreauYosida
  simp only [ereal_iSup_sub_real,ereal_toENNReal_iSup,← EReal.coe_sub,
    EReal.real_coe_toENNReal]

lemma moreauGain_eq_supported_penalty_sup {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : E → ℝ) (p γ : ℝ) (hγ : 0 ≤ γ) (ξ : E) :
    moreauGain Ξ ℓ p γ ξ = ⨆ z : E,
      ENNReal.ofReal (supportedGain Ξ ℓ (z,ξ) - γ * supportedCost Ξ p (z,ξ)) := by
  classical
  rw [moreauGain_eq_score_sup]
  apply iSup_congr
  intro z
  by_cases hz : z ∈ Ξ
  · simp only [hz,iSup_pos,supportedGain,supportedCost,if_true]
    have hr : ℓ z - γ * ‖z-ξ‖ ^ p - ℓ ξ = (ℓ z-ℓ ξ) - γ * ‖z-ξ‖ ^ p := by ring
    rw [hr,clipped_penalty_ofReal_eq _ _ (mul_nonneg hγ (Real.rpow_nonneg (norm_nonneg _) p))]
  · simp [hz,supportedGain,supportedCost]

lemma countable_moreauGain_envelope {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E] (Ξ : Set E) (ℓ : E → ℝ) (p : ℝ) (hp : 0 ≤ p) :
    ∃ T : Set Ξ, T.Countable ∧ ∀ (ξ : E) (γ : ℝ), 0 ≤ γ →
      moreauGain Ξ ℓ p γ ξ = ⨆ z : Ξ, ⨆ (_ : z ∈ T),
        ENNReal.ofReal (max (ℓ z - ℓ ξ) 0 - γ * ‖(z:E)-ξ‖ ^ p) := by
  obtain ⟨T,hTc,hrep⟩ := countable_moreau_envelope Ξ ℓ p hp
  refine ⟨T,hTc,fun ξ γ hγ => ?_⟩
  unfold moreauGain
  rw [hrep ξ γ]
  simp only [ereal_iSup_sub_real,ereal_toENNReal_iSup,← EReal.coe_sub,
    EReal.real_coe_toENNReal]
  apply iSup_congr
  intro z
  apply iSup_congr
  intro hz
  have hr : ℓ z - γ * ‖(z:E)-ξ‖ ^ p - ℓ ξ = (ℓ z-ℓ ξ) - γ * ‖(z:E)-ξ‖ ^ p := by ring
  rw [hr,clipped_penalty_ofReal_eq _ _ (mul_nonneg hγ (Real.rpow_nonneg (norm_nonneg _) p))]

#print axioms clipped_penalty_ofReal_eq
#print axioms moreauGain_eq_score_sup
#print axioms moreauGain_eq_supported_penalty_sup
#print axioms countable_moreauGain_envelope
end DualityCodex

-- Complete local proof: Solutions.Duality_SelectorRisk
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma nominalRisk_map_add_gain {Z E : Type*} [MeasurableSpace Z] [MeasurableSpace E]
    (π : Measure Z) (T : Z → E) (hT : Measurable T)
    (ℓ : E → ℝ) (hl : Measurable ℓ) (b g : Z → ℝ)
    (hb : Integrable b π) (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hidentity : ∀ z, ℓ (T z) = b z + g z) :
    nominalRisk (π.map T) ℓ = (∫ z, b z ∂π : ℝ) +
      ((∫⁻ z, ENNReal.ofReal (g z) ∂π : ENNReal) : EReal) := by
  unfold nominalRisk
  rw [erealExpectation_map π T hT (fun y => (ℓ y : EReal)) hl.coe_real_ereal]
  simp only [hidentity]
  exact erealExpectation_add_nonnegative π b g hb hg hg0

#print axioms nominalRisk_map_add_gain
end DualityCodex

-- Complete local proof: Solutions.Duality_TransportBudget
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma wasserstein_budget_iff {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (Q P : Measure E) (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) :
    wassersteinDistance p Q P ≤ ENNReal.ofReal ε ↔
      (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
        ∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) ≤ ENNReal.ofReal (ε ^ p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  constructor
  · intro h
    have hr := ENNReal.rpow_le_rpow h hp0.le
    unfold wassersteinDistance at hr
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg hε hp0.le] at hr
    exact hr
  · intro h
    unfold wassersteinDistance
    apply (ENNReal.rpow_le_rpow h (one_div_pos.mpr hp0).le).trans
    rw [← ENNReal.ofReal_rpow_of_nonneg hε hp0.le, ← ENNReal.rpow_mul,
      mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

lemma wasserstein_le_of_coupling_cost {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] (Q P : Measure E) (π : Measure (E × E))
    (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = P)
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p)
    (hc : (∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) ≤ ENNReal.ofReal (ε ^ p)) :
    wassersteinDistance p Q P ≤ ENNReal.ofReal ε := by
  apply (wasserstein_budget_iff Q P ε p hε hp).mpr
  exact (iInf_le_of_le π (iInf_le_of_le hπ le_rfl)).trans hc

#print axioms wasserstein_budget_iff
#print axioms wasserstein_le_of_coupling_cost
end DualityCodex

-- Complete local proof: Solutions.Duality_SupportedCoupling
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma supportedFallback_second_marginal {E : Type*} [MeasurableSpace E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (π : Measure (E × E)) :
    (π.map (supportedFallback Ξ ℓ)).map Prod.snd = π.map Prod.snd := by
  rw [Measure.map_map measurable_snd (measurable_supportedFallback Ξ hΞ ℓ hl)]
  congr 1
  funext z
  exact supportedFallback_snd Ξ ℓ z

lemma supportedFallback_first_marginal {E : Type*} [MeasurableSpace E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (π : Measure (E × E)) :
    (π.map (supportedFallback Ξ ℓ)).map Prod.fst =
      π.map (fun z => (supportedFallback Ξ ℓ z).1) :=
  Measure.map_map measurable_fst (measurable_supportedFallback Ξ hΞ ℓ hl)

lemma supportedFallback_first_supported {E : Type*} [MeasurableSpace E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) (hPΞ : P Ξᶜ = 0) (π : Measure (E × E))
    (hs : π.map Prod.snd = P) :
    (π.map (fun z => (supportedFallback Ξ ℓ z).1)) Ξᶜ = 0 := by
  have hae : ∀ᵐ z ∂π, z.2 ∈ Ξ := by
    apply ae_iff.mpr
    change π (Prod.snd ⁻¹' Ξᶜ) = 0
    rw [← Measure.map_apply measurable_snd hΞ.compl,hs,hPΞ]
  rw [Measure.map_apply (f := fun z => (supportedFallback Ξ ℓ z).1)
    (measurable_fst.comp (measurable_supportedFallback Ξ hΞ ℓ hl))
    hΞ.compl]
  exact ae_iff.mp (hae.mono fun z hz => supportedFallback_supported Ξ ℓ z hz)

lemma supportedFallback_cost_integral_le {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (p : ℝ) (hp : 0 < p) (π : Measure (E × E)) :
    (∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π.map (supportedFallback Ξ ℓ)) ≤
      ∫⁻ z, ENNReal.ofReal (supportedCost Ξ p z) ∂π := by
  have hm : Measurable (fun z : E × E => ENNReal.ofReal (‖z.1-z.2‖ ^ p)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_fst.sub continuous_snd).norm.rpow_const (fun _ => Or.inr hp.le)).measurable
  rw [lintegral_map hm (measurable_supportedFallback Ξ hΞ ℓ hl)]
  exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal
    (supportedFallback_cost_le Ξ ℓ p hp z)

lemma supportedFallback_risk {E : Type*} [MeasurableSpace E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) (π : Measure (E × E)) (hs : π.map Prod.snd = P)
    (hP : Integrable ℓ P) :
    nominalRisk (π.map (fun z => (supportedFallback Ξ ℓ z).1)) ℓ =
      (∫ y, ℓ y ∂P : ℝ) +
        ((∫⁻ z, ENNReal.ofReal (supportedGain Ξ ℓ z) ∂π : ENNReal) : EReal) := by
  have hPs : Integrable ℓ (π.map Prod.snd) := by rwa [hs]
  have hb : Integrable (fun z : E × E => ℓ z.2) π := hPs.comp_measurable measurable_snd
  have hi : (∫ z : E × E, ℓ z.2 ∂π) = ∫ y, ℓ y ∂P := by
    rw [← hs]
    exact (integral_map_of_stronglyMeasurable measurable_snd hl.stronglyMeasurable).symm
  have h := nominalRisk_map_add_gain π (fun z => (supportedFallback Ξ ℓ z).1)
    (measurable_fst.comp (measurable_supportedFallback Ξ hΞ ℓ hl)) ℓ hl
    (fun z => ℓ z.2) (supportedGain Ξ ℓ) hb (measurable_supportedGain Ξ hΞ ℓ hl)
    (supportedGain_nonnegative Ξ ℓ) (supportedFallback_gain Ξ ℓ)
  simpa only [hi] using h

lemma supportedFallback_in_ambiguity {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) (hPΞ : P Ξᶜ = 0) (π : Measure (E × E)) [IsProbabilityMeasure π]
    (hs : π.map Prod.snd = P) (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p)
    (hc : (∫⁻ z, ENNReal.ofReal (supportedCost Ξ p z) ∂π) ≤ ENNReal.ofReal (ε ^ p)) :
    π.map (fun z => (supportedFallback Ξ ℓ z).1) ∈ ambiguitySet ε p Ξ P := by
  have hF := measurable_supportedFallback Ξ hΞ ℓ hl
  have hT := measurable_fst.comp hF
  have hprob := π.isProbabilityMeasure_map hT.aemeasurable
  refine ⟨hprob.measure_univ,supportedFallback_first_supported Ξ hΞ ℓ hl P hPΞ π hs,?_⟩
  apply wasserstein_le_of_coupling_cost _ P (π.map (supportedFallback Ξ ℓ))
    ⟨supportedFallback_first_marginal Ξ hΞ ℓ hl π,
      (supportedFallback_second_marginal Ξ hΞ ℓ hl π).trans hs⟩ ε p hε hp
  exact (supportedFallback_cost_integral_le Ξ hΞ ℓ hl p
    (lt_of_lt_of_le zero_lt_one hp) π).trans hc

lemma supported_gain_le_worstCaseRisk {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) (hPΞ : P Ξᶜ = 0) (hP : Integrable ℓ P)
    (π : Measure (E × E)) [IsProbabilityMeasure π] (hs : π.map Prod.snd = P)
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p)
    (hc : (∫⁻ z, ENNReal.ofReal (supportedCost Ξ p z) ∂π) ≤ ENNReal.ofReal (ε ^ p)) :
    (∫ y, ℓ y ∂P : ℝ) +
      ((∫⁻ z, ENNReal.ofReal (supportedGain Ξ ℓ z) ∂π : ENNReal) : EReal) ≤
      worstCaseRisk ε p Ξ P ℓ := by
  rw [← supportedFallback_risk Ξ hΞ ℓ hl P π hs hP]
  exact le_iSup_of_le (π.map (fun z => (supportedFallback Ξ ℓ z).1))
    (le_iSup_of_le (supportedFallback_in_ambiguity Ξ hΞ ℓ hl P hPΞ π hs ε p hε hp hc)
      le_rfl)

#print axioms supportedFallback_second_marginal
#print axioms supportedFallback_first_marginal
#print axioms supportedFallback_first_supported
#print axioms supportedFallback_cost_integral_le
#print axioms supportedFallback_risk
#print axioms supportedFallback_in_ambiguity
#print axioms supported_gain_le_worstCaseRisk
end DualityCodex

-- Complete local proof: Solutions.Duality_DiagonalValues
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma supportedGain_diagonal {E : Type*} (Ξ : Set E) (ℓ : E → ℝ) (x : E) :
    supportedGain Ξ ℓ (x,x) = 0 := by
  simp [supportedGain]

lemma supportedCost_diagonal {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (p : ℝ) (hp : 0 < p) (x : E) :
    supportedCost Ξ p (x,x) = 0 := by
  simp [supportedCost, Real.zero_rpow hp.ne']

lemma supported_values_diagonal {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hΞ : MeasurableSet Ξ)
    (ℓ : E → ℝ) (hl : Measurable ℓ) (p : ℝ) (hp : 0 < p) :
    (0,0) ∈ couplingValueSet P (fun z => ENNReal.ofReal (supportedCost Ξ p z))
      (fun z => ENNReal.ofReal (supportedGain Ξ ℓ z)) := by
  let d : E → E × E := fun x => (x,x)
  have hd : Measurable d := measurable_id.prodMk measurable_id
  let π := P.map d
  have hπ : IsProbabilityMeasure π := P.isProbabilityMeasure_map hd.aemeasurable
  have hs : π.map Prod.snd = P := by
    dsimp [π]
    rw [Measure.map_map measurable_snd hd]
    exact Measure.map_id'
  have hc : (∫⁻ z, ENNReal.ofReal (supportedCost Ξ p z) ∂π) = 0 := by
    dsimp [π]
    rw [lintegral_map (f := fun z => ENNReal.ofReal (supportedCost Ξ p z)) (ENNReal.measurable_ofReal.comp
      (measurable_supportedCost Ξ hΞ p hp.le)) hd]
    simp only [d, supportedCost_diagonal Ξ p hp, ENNReal.ofReal_zero, lintegral_zero]
  have hg : (∫⁻ z, ENNReal.ofReal (supportedGain Ξ ℓ z) ∂π) = 0 := by
    dsimp [π]
    rw [lintegral_map (f := fun z => ENNReal.ofReal (supportedGain Ξ ℓ z)) (ENNReal.measurable_ofReal.comp
      (measurable_supportedGain Ξ hΞ ℓ hl)) hd]
    simp only [d, supportedGain_diagonal, ENNReal.ofReal_zero, lintegral_zero]
  refine ⟨π,hπ,hs,?_,?_,?_⟩
  · rw [hc]; exact ENNReal.zero_ne_top
  · rw [hg]; exact ENNReal.zero_ne_top
  · simp [hc,hg]

#print axioms supportedGain_diagonal
#print axioms supportedCost_diagonal
#print axioms supported_values_diagonal
end DualityCodex

-- Complete local proof: Solutions.Duality_MomentSupport
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma supported_moment_budget_bound {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) (hPΞ : P Ξᶜ = 0) (hP : Integrable ℓ P)
    (ε p V : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p)
    (hupper : worstCaseRisk ε p Ξ P ℓ ≤ ((∫ y, ℓ y ∂P) + V : ℝ)) :
    ∀ v ∈ couplingValueSet P (fun z => ENNReal.ofReal (supportedCost Ξ p z))
      (fun z => ENNReal.ofReal (supportedGain Ξ ℓ z)), v.1 < ε ^ p → v.2 ≤ V := by
  rintro v ⟨π,hprob,hs,hcf,hgf,rfl⟩ hcost
  letI := hprob
  have hc : (∫⁻ z, ENNReal.ofReal (supportedCost Ξ p z) ∂π) ≤ ENNReal.ofReal (ε ^ p) :=
    (ENNReal.le_ofReal_iff_toReal_le hcf (Real.rpow_nonneg hε p)).mpr hcost.le
  have h := (supported_gain_le_worstCaseRisk Ξ hΞ ℓ hl P hPΞ hP π hs ε p hε hp hc).trans hupper
  rw [← EReal.coe_ennreal_toReal hgf, ← EReal.coe_add] at h
  have hr := EReal.coe_le_coe_iff.mp h
  linarith

lemma exists_supported_multiplier {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) [IsProbabilityMeasure P] (hPΞ : P Ξᶜ = 0) (hP : Integrable ℓ P)
    (ε p V : ℝ) (hε : 0 < ε) (hp : 1 ≤ p)
    (hupper : worstCaseRisk ε p Ξ P ℓ ≤ ((∫ y, ℓ y ∂P) + V : ℝ)) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ v ∈ couplingValueSet P
        (fun z => ENNReal.ofReal (supportedCost Ξ p z))
        (fun z => ENNReal.ofReal (supportedGain Ξ ℓ z)),
      v.2 ≤ V + γ * (v.1 - ε ^ p) := by
  exact supporting_multiplier _ (couplingValueSet_convex P _ _) (ε ^ p) V 0
    (Real.rpow_pos_of_pos hε p)
    (supported_values_diagonal P Ξ hΞ ℓ hl p (lt_of_lt_of_le zero_lt_one hp))
    (supported_moment_budget_bound Ξ hΞ ℓ hl P hPΞ hP ε p V hε.le hp hupper)

#print axioms supported_moment_budget_bound
#print axioms exists_supported_multiplier
end DualityCodex

-- Complete local proof: Solutions.Duality_StrongFinite
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma moreauGain_integral_le_of_support {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) [IsProbabilityMeasure P] (p γ α : ℝ) (hp : 0 < p)
    (hγ : 0 ≤ γ) (hα : 0 ≤ α)
    (hsupport : ∀ v ∈ couplingValueSet P (fun z => ENNReal.ofReal (supportedCost Ξ p z))
      (fun z => ENNReal.ofReal (supportedGain Ξ ℓ z)), v.2 - γ * v.1 ≤ α) :
    (∫⁻ y, moreauGain Ξ ℓ p γ y ∂P) ≤ ENNReal.ofReal α := by
  classical
  obtain ⟨T,hTc,hrep⟩ := countable_moreauGain_envelope Ξ ℓ p hp.le
  letI : Countable T := hTc.to_subtype
  let z : T → E := fun i => i.val.val
  have he : ∀ y, moreauGain Ξ ℓ p γ y = ⨆ i : T,
      ENNReal.ofReal (supportedGain Ξ ℓ (z i,y) - γ * supportedCost Ξ p (z i,y)) := by
    intro y
    rw [hrep y γ hγ,← iSup_subtype'']
    apply iSup_congr
    intro i
    have hz : z i ∈ Ξ := i.val.property
    simp [supportedGain,supportedCost,hz,z]
  simp_rw [he]
  exact uncapped_envelope_integral_le P (supportedGain Ξ ℓ) (supportedCost Ξ p)
    (measurable_supportedGain Ξ hΞ ℓ hl) (measurable_supportedCost Ξ hΞ p hp.le)
    (supportedGain_nonnegative Ξ ℓ) (supportedCost_nonnegative Ξ p)
    (supportedGain_diagonal Ξ ℓ) (supportedCost_diagonal Ξ p hp)
    γ α hα z hsupport

lemma exists_dual_le_finite_upper {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) [IsProbabilityMeasure P] (hPΞ : P Ξᶜ = 0) (hP : Integrable ℓ P)
    (ε p V : ℝ) (hε : 0 < ε) (hp : 1 ≤ p)
    (hupper : worstCaseRisk ε p Ξ P ℓ ≤ ((∫ y, ℓ y ∂P) + V : ℝ)) :
    ∃ γ : ℝ, 0 ≤ γ ∧
      erealExpectation P (moreauYosida Ξ ℓ p γ) + ((γ * ε ^ p : ℝ) : EReal) ≤
        ((∫ y, ℓ y ∂P) + V : ℝ) := by
  obtain ⟨γ,hγ,hbound⟩ := exists_supported_multiplier Ξ hΞ ℓ hl P hPΞ hP ε p V hε hp hupper
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let α := V - γ * ε ^ p
  have hα : 0 ≤ α := by
    have hb := hbound (0,0) (supported_values_diagonal P Ξ hΞ ℓ hl p hp0)
    dsimp [α]
    dsimp only at hb
    linarith
  have hs : ∀ v ∈ couplingValueSet P (fun z => ENNReal.ofReal (supportedCost Ξ p z))
      (fun z => ENNReal.ofReal (supportedGain Ξ ℓ z)), v.2 - γ * v.1 ≤ α := by
    intro v hv
    have hb := hbound v hv
    dsimp [α]
    linarith
  have hg := moreauGain_integral_le_of_support Ξ hΞ ℓ hl P p γ α hp0 hγ hα hs
  have hge : ((∫⁻ y, moreauGain Ξ ℓ p γ y ∂P : ENNReal) : EReal) ≤ (α : EReal) := by
    have hh := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hg
    rw [EReal.coe_ennreal_ofReal,max_eq_left hα] at hh
    exact hh
  refine ⟨γ,hγ,?_⟩
  rw [moreau_expectation_eq_baseline_add_gain Ξ ℓ hl p γ hp0 P hPΞ hP]
  apply (add_le_add (add_le_add le_rfl hge) le_rfl).trans
  rw [← EReal.coe_add,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  dsimp [α]
  linarith

lemma nominal_integral_le_worstCaseRisk {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) [IsProbabilityMeasure P] (hPΞ : P Ξᶜ = 0) (hP : Integrable ℓ P)
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) :
    (∫ y, ℓ y ∂P : ℝ) ≤ worstCaseRisk ε p Ξ P ℓ := by
  obtain ⟨π,hπ,hs,hcf,hgf,he⟩ := supported_values_diagonal P Ξ hΞ ℓ hl p
    (lt_of_lt_of_le zero_lt_one hp)
  letI := hπ
  have hz := congrArg Prod.fst he
  dsimp only at hz
  have hc : (∫⁻ z, ENNReal.ofReal (supportedCost Ξ p z) ∂π) ≤ ENNReal.ofReal (ε ^ p) := by
    apply (ENNReal.le_ofReal_iff_toReal_le hcf (Real.rpow_nonneg hε p)).mpr
    rw [← hz]
    exact Real.rpow_nonneg hε p
  have hb := supported_gain_le_worstCaseRisk Ξ hΞ ℓ hl P hPΞ hP π hs ε p hε hp hc
  apply le_trans _ hb
  simpa only [add_zero] using
    add_le_add (le_refl ((∫ y, ℓ y ∂P : ℝ) : EReal))
      (EReal.coe_ennreal_nonneg (∫⁻ z, ENNReal.ofReal (supportedGain Ξ ℓ z) ∂π))

#print axioms moreauGain_integral_le_of_support
#print axioms exists_dual_le_finite_upper
#print axioms nominal_integral_le_worstCaseRisk
end DualityCodex

-- Complete local proof: Solutions.Duality_WeakCoupling
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma loss_le_baseline_gain_cost {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : E → ℝ) (p γ : ℝ) (hp : 0 < p) (hγ : 0 ≤ γ)
    (z : E × E) (hx : z.1 ∈ Ξ) (hy : z.2 ∈ Ξ) :
    (ℓ z.1 : EReal) ≤ (ℓ z.2 : EReal) +
      ((moreauGain Ξ ℓ p γ z.2 + ENNReal.ofReal (γ * ‖z.1-z.2‖ ^ p) : ENNReal) : EReal) := by
  have hscore : ((ℓ z.1 - γ * ‖z.1-z.2‖ ^ p : ℝ) : EReal) ≤
      moreauYosida Ξ ℓ p γ z.2 := le_iSup_of_le z.1 (le_iSup_of_le hx le_rfl)
  rw [EReal.coe_sub] at hscore
  have h := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp hscore
  rw [moreau_eq_baseline_add_gain Ξ ℓ p γ hp z.2 hy] at h
  have hcost : ((γ * ‖z.1-z.2‖ ^ p : ℝ) : EReal) =
      (ENNReal.ofReal (γ * ‖z.1-z.2‖ ^ p) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left (mul_nonneg hγ (Real.rpow_nonneg (norm_nonneg _) p))]
  rw [hcost, add_assoc, ← EReal.coe_ennreal_add] at h
  exact h

lemma weak_coupling_risk_bound {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P Q : Measure E) (hPΞ : P Ξᶜ = 0) (hQΞ : Q Ξᶜ = 0) (hP : Integrable ℓ P)
    (π : Measure (E × E)) (hfst : π.map Prod.fst = Q) (hsnd : π.map Prod.snd = P)
    (p γ : ℝ) (hp : 0 < p) (hγ : 0 ≤ γ) :
    nominalRisk Q ℓ ≤ (∫ y, ℓ y ∂P : ℝ) +
      (((∫⁻ y, moreauGain Ξ ℓ p γ y ∂P) + ENNReal.ofReal γ *
        (∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) : ENNReal) : EReal) := by
  have hX : ∀ᵐ z ∂π, z.1 ∈ Ξ := by
    apply ae_iff.mpr
    change π (Prod.fst ⁻¹' Ξᶜ) = 0
    rw [← Measure.map_apply measurable_fst hΞ.compl,hfst,hQΞ]
  have hY : ∀ᵐ z ∂π, z.2 ∈ Ξ := by
    apply ae_iff.mpr
    change π (Prod.snd ⁻¹' Ξᶜ) = 0
    rw [← Measure.map_apply measurable_snd hΞ.compl,hsnd,hPΞ]
  have hPs : Integrable ℓ (π.map Prod.snd) := by rwa [hsnd]
  have hb : Integrable (fun z : E × E => ℓ z.2) π := hPs.comp_measurable measurable_snd
  have hi : (∫ z : E × E, ℓ z.2 ∂π) = ∫ y, ℓ y ∂P := by
    rw [← hsnd]
    exact (integral_map_of_stronglyMeasurable measurable_snd hl.stronglyMeasurable).symm
  have hcm : Measurable (fun z : E × E => ENNReal.ofReal (‖z.1-z.2‖ ^ p)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_fst.sub continuous_snd).norm.rpow_const (fun _ => Or.inr hp.le)).measurable
  have hgm : Measurable (fun z : E × E => moreauGain Ξ ℓ p γ z.2 +
      ENNReal.ofReal (γ * ‖z.1-z.2‖ ^ p)) :=
    ((moreauGain_measurable Ξ ℓ hl p γ hp.le).comp measurable_snd).add
      (ENNReal.measurable_ofReal.comp
        (continuous_const.mul ((continuous_fst.sub continuous_snd).norm.rpow_const
          (fun _ => Or.inr hp.le))).measurable)
  unfold nominalRisk
  rw [← hfst, erealExpectation_map π Prod.fst measurable_fst
    (fun y : E => (ℓ y : EReal)) hl.coe_real_ereal]
  have hbound := erealExpectation_mono π (fun z : E × E => (ℓ z.1 : EReal))
    (fun z => (ℓ z.2 : EReal) +
      ((moreauGain Ξ ℓ p γ z.2 + ENNReal.ofReal (γ * ‖z.1-z.2‖ ^ p) : ENNReal) : EReal))
    ((hX.and hY).mono fun z h => loss_le_baseline_gain_cost Ξ ℓ p γ hp hγ z h.1 h.2)
  rw [erealExpectation_add_ennreal π (fun z => ℓ z.2) _ hb hgm,hi] at hbound
  have hgain : (∫⁻ z : E × E, moreauGain Ξ ℓ p γ z.2 ∂π) =
      ∫⁻ y, moreauGain Ξ ℓ p γ y ∂P := by
    rw [← hsnd]
    exact (lintegral_map (moreauGain_measurable Ξ ℓ hl p γ hp.le) measurable_snd).symm
  have hcost : (∫⁻ z : E × E, ENNReal.ofReal (γ * ‖z.1-z.2‖ ^ p) ∂π) =
      ENNReal.ofReal γ * ∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π := by
    simp only [ENNReal.ofReal_mul hγ]
    exact lintegral_const_mul _ hcm
  rw [lintegral_add_left (f := fun z : E × E => moreauGain Ξ ℓ p γ z.2)
    ((moreauGain_measurable Ξ ℓ hl p γ hp.le).comp measurable_snd),
    hgain,hcost] at hbound
  exact hbound

#print axioms loss_le_baseline_gain_cost
#print axioms weak_coupling_risk_bound
end DualityCodex

-- Complete local proof: Solutions.Duality_WeakDuality
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma exists_coupling_power_cost_lt {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (Q P : Measure E) (ε p η : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (hη : 0 < η)
    (hw : wassersteinDistance p Q P ≤ ENNReal.ofReal ε) :
    ∃ π : Measure (E × E), (π.map Prod.fst = Q ∧ π.map Prod.snd = P) ∧
      (∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) < ENNReal.ofReal (ε ^ p + η) := by
  have hcost := (wasserstein_budget_iff Q P ε p hε hp).mp hw
  have hlt : (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
      ∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) < ENNReal.ofReal (ε ^ p + η) :=
    lt_of_le_of_lt hcost ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.rpow_nonneg hε p)).mpr
      (by linarith))
  rw [iInf_lt_iff] at hlt
  obtain ⟨π,hπ⟩ := hlt
  rw [iInf_lt_iff] at hπ
  obtain ⟨hm,hc⟩ := hπ
  exact ⟨π,hm,hc⟩

lemma nominalRisk_le_dual_of_ambiguity {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) (hPΞ : P Ξᶜ = 0) (hP : Integrable ℓ P)
    (ε p γ : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (hγ : 0 ≤ γ)
    (Q : Measure E) (hQ : Q ∈ ambiguitySet ε p Ξ P) :
    nominalRisk Q ℓ ≤ erealExpectation P (moreauYosida Ξ ℓ p γ) + ((γ * ε ^ p : ℝ) : EReal) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases htop : (∫⁻ y, moreauGain Ξ ℓ p γ y ∂P) = ⊤
  · rw [moreau_expectation_eq_baseline_add_gain Ξ ℓ hl p γ hp0 P hPΞ hP,htop,
      EReal.coe_ennreal_top,EReal.coe_add_top,EReal.top_add_coe]
    exact le_top
  · rw [moreau_expectation_eq_baseline_add_gain Ξ ℓ hl p γ hp0 P hPΞ hP,
      ← EReal.coe_ennreal_toReal htop,← EReal.coe_add,← EReal.coe_add]
    apply EReal.le_of_forall_lt_iff_le.mp
    intro r hr
    have hr' := EReal.coe_lt_coe_iff.mp hr
    let ζ := r - ((∫ y, ℓ y ∂P) + (∫⁻ y, moreauGain Ξ ℓ p γ y ∂P).toReal + γ * ε ^ p)
    have hζ : 0 < ζ := by dsimp [ζ]; linarith
    let η := ζ / (γ+1)
    have hγ1 : 0 < γ+1 := by linarith
    have hη : 0 < η := div_pos hζ hγ1
    obtain ⟨π,hm,hc⟩ := exists_coupling_power_cost_lt Q P ε p η hε hp hη hQ.2.2
    have hcf : (∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) ≠ ⊤ := (lt_of_lt_of_le hc le_top).ne
    have hsum : (∫⁻ y, moreauGain Ξ ℓ p γ y ∂P) + ENNReal.ofReal γ *
        (∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨htop,ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcf⟩
    have hweak := weak_coupling_risk_bound Ξ hΞ ℓ hl P Q hPΞ hQ.2.1 hP π hm.1 hm.2 p γ hp0 hγ
    rw [← EReal.coe_ennreal_toReal hsum,
      ENNReal.toReal_add htop (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcf),
      ENNReal.toReal_mul,ENNReal.toReal_ofReal hγ,← EReal.coe_add] at hweak
    have hcostreal := ENNReal.toReal_lt_of_lt_ofReal hc
    have hscale := mul_le_mul_of_nonneg_left hcostreal.le hγ
    have he : η * (γ+1) = ζ := div_mul_cancel₀ ζ hγ1.ne'
    have hγeta : γ * η ≤ ζ := by nlinarith [hη.le]
    apply hweak.trans
    apply EReal.coe_le_coe_iff.mpr
    dsimp [ζ] at he hγeta
    nlinarith

lemma worstCaseRisk_le_dual {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) (hPΞ : P Ξᶜ = 0) (hP : Integrable ℓ P)
    (ε p γ : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (hγ : 0 ≤ γ) :
    worstCaseRisk ε p Ξ P ℓ ≤
      erealExpectation P (moreauYosida Ξ ℓ p γ) + ((γ * ε ^ p : ℝ) : EReal) := by
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  exact nominalRisk_le_dual_of_ambiguity Ξ hΞ ℓ hl P hPΞ hP ε p γ hε hp hγ Q hQ

lemma worstCaseRisk_le_dual_inf {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (ℓ : E → ℝ) (hl : Measurable ℓ)
    (P : Measure E) (hPΞ : P Ξᶜ = 0) (hP : Integrable ℓ P)
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) :
    worstCaseRisk ε p Ξ P ℓ ≤ ⨅ (γ : ℝ) (_ : 0 ≤ γ),
      erealExpectation P (moreauYosida Ξ ℓ p γ) + ((γ * ε ^ p : ℝ) : EReal) := by
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  exact worstCaseRisk_le_dual Ξ hΞ ℓ hl P hPΞ hP ε p γ hε hp hγ

#print axioms exists_coupling_power_cost_lt
#print axioms nominalRisk_le_dual_of_ambiguity
#print axioms worstCaseRisk_le_dual
#print axioms worstCaseRisk_le_dual_inf
end DualityCodex

-- Complete local proof: Solutions.Sol_WassersteinDRO_Duality_strong_duality_worst_case_risk_v2
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Duality

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ε p : ℝ) (hε : 0 < ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞcl : IsClosed Ξ)
    (PN : Measure E) [IsProbabilityMeasure PN] (hPNΞ : PN Ξᶜ = 0)
    (ℓ : E → ℝ) (hℓm : Measurable ℓ) (hℓusc : UpperSemicontinuous ℓ) (hℓ : Integrable ℓ PN) :
    worstCaseRisk ε p Ξ PN ℓ =
      ⨅ (γ : ℝ) (_ : 0 ≤ γ),
        erealExpectation PN (moreauYosida Ξ ℓ p γ) + ((γ * ε ^ p : ℝ) : EReal) := by
  apply le_antisymm
    (DualityCodex.worstCaseRisk_le_dual_inf Ξ hΞcl.measurableSet ℓ hℓm PN hPNΞ hℓ ε p hε.le hp)
  by_cases htop : worstCaseRisk ε p Ξ PN ℓ = ⊤
  · rw [htop]
    exact le_top
  · have hnom := DualityCodex.nominal_integral_le_worstCaseRisk Ξ hΞcl.measurableSet
      ℓ hℓm PN hPNΞ hℓ ε p hε.le hp
    have hbot : worstCaseRisk ε p Ξ PN ℓ ≠ ⊥ := by
      intro hbot
      rw [hbot] at hnom
      exact (EReal.coe_ne_bot _) (le_bot_iff.mp hnom)
    obtain ⟨r,hr⟩ := EReal.canLift.prf (worstCaseRisk ε p Ξ PN ℓ) ⟨htop,hbot⟩
    have hupper : worstCaseRisk ε p Ξ PN ℓ ≤
        (((∫ y, ℓ y ∂PN) + (r - (∫ y, ℓ y ∂PN)) : ℝ) : EReal) := by
      rw [← hr]
      apply EReal.coe_le_coe_iff.mpr
      linarith
    obtain ⟨γ,hγ,hdual⟩ := DualityCodex.exists_dual_le_finite_upper Ξ hΞcl.measurableSet
      ℓ hℓm PN hPNΞ hℓ ε p (r - (∫ y, ℓ y ∂PN)) hε hp hupper
    apply iInf_le_of_le γ
    apply iInf_le_of_le hγ
    calc
      erealExpectation PN (moreauYosida Ξ ℓ p γ) + ((γ * ε ^ p : ℝ) : EReal) ≤
          (((∫ y, ℓ y ∂PN) + (r - (∫ y, ℓ y ∂PN)) : ℝ) : EReal) := hdual
      _ = (r : EReal) := by congr 1; ring
      _ = worstCaseRisk ε p Ξ PN ℓ := hr

#print axioms solution
