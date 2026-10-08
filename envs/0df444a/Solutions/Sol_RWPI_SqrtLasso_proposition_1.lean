-- Prove2me | solution 1 for RWPI.SqrtLasso.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T09:11:04.530402+00:00
-- url     : https://prove2.me/submissions/231d271c-bafb-44fe-80e8-32c590f1bba5

import Definitions.Def_RWPI_SqrtLasso_phi
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_RWPI_SqrtLasso_worstCase
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Mathlib

set_option autoImplicit false
namespace TransportCodex
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
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
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
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open RWPI.SqrtLasso

lemma coupling_loss_le_worstCase {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) (c : Z → Z → ENNReal) (l : Z → ℝ)
    (hl : Measurable (fun z => ENNReal.ofReal (l z))) (δ : ℝ)
    (π : Measure (Z × Z)) (hπ : IsProbabilityMeasure π) (hs : π.map Prod.snd = Q)
    (hc : (∫⁻ z, c z.1 z.2 ∂π) ≤ ENNReal.ofReal δ) :
    (∫⁻ z, ENNReal.ofReal (l z.1) ∂π) ≤ worstCase c δ Q l := by
  letI := hπ
  have hp : IsProbabilityMeasure (π.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hcost : transportCost c (π.map Prod.fst) Q ≤ ∫⁻ z, c z.1 z.2 ∂π := by
    unfold transportCost
    exact iInf_le_of_le π (iInf_le_of_le ⟨hπ, rfl, hs⟩ le_rfl)
  have hbudget := hcost.trans hc
  have he : (∫⁻ z, ENNReal.ofReal (l z) ∂π.map Prod.fst) ≤ worstCase c δ Q l := by
    unfold worstCase
    exact le_iSup_of_le (π.map Prod.fst) (le_iSup_of_le ⟨hp, hbudget⟩ le_rfl)
  rwa [lintegral_map hl measurable_fst] at he

lemma couplingValueSet_budget {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) (c : Z → Z → ENNReal) (l : Z → ℝ)
    (hl : Measurable (fun z => ENNReal.ofReal (l z))) (δ : ℝ)
    (hfinite : worstCase c δ Q l ≠ ⊤) :
    ∀ v ∈ couplingValueSet Q (fun z => c z.1 z.2) (fun z => ENNReal.ofReal (l z.1)),
      v.1 < δ → v.2 ≤ (worstCase c δ Q l).toReal := by
  rintro v ⟨π, hπ, hs, hcost, hloss, rfl⟩ hv
  have hδ : 0 ≤ δ := ENNReal.toReal_nonneg.trans hv.le
  have hc : (∫⁻ z, c z.1 z.2 ∂π) ≤ ENNReal.ofReal δ :=
    (ENNReal.le_ofReal_iff_toReal_le hcost hδ).mpr hv.le
  exact ENNReal.toReal_mono hfinite (coupling_loss_le_worstCase Q c l hl δ π hπ hs hc)

#print axioms coupling_loss_le_worstCase
#print axioms couplingValueSet_budget
end TransportCodex

set_option autoImplicit false
namespace TransportCodex

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
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open WassersteinDRO.Regularization

lemma empirical_probability {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (hn : 0 < n) (X : Fin n → Z) : IsProbabilityMeasure (empiricalDistribution X) := by
  constructor
  simp [empiricalDistribution, Measure.smul_apply, Measure.finsetSum_apply]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

lemma empirical_map {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W] {n : ℕ}
    (X : Fin n → Z) (f : Z → W) (hf : Measurable f) :
    (empiricalDistribution X).map f = empiricalDistribution (fun i => f (X i)) := by
  unfold empiricalDistribution
  rw [Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable]
  simp only [Measure.map_dirac' hf]

lemma empirical_lintegral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (f : Z → ENNReal) :
    (∫⁻ z, f z ∂empiricalDistribution X) = (n : ENNReal)⁻¹ * ∑ i, f (X i) := by
  unfold empiricalDistribution
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac]
  rfl

lemma empirical_coupling {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (Y : Fin n → W) :
    IsProbabilityMeasure (empiricalDistribution (fun i => (X i, Y i))) ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.fst = empiricalDistribution X ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.snd = empiricalDistribution Y := by
  refine ⟨empirical_probability hn _, ?_, ?_⟩
  · exact empirical_map _ Prod.fst measurable_fst
  · exact empirical_map _ Prod.snd measurable_snd

lemma transportCost_le_empirical_cost {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (hn : 0 < n) (X Y : Fin n → Z)
    (c : Z → Z → ENNReal) :
    RWPI.SqrtLasso.transportCost c (empiricalDistribution X) (empiricalDistribution Y) ≤
      (n : ENNReal)⁻¹ * ∑ i, c (X i) (Y i) := by
  unfold RWPI.SqrtLasso.transportCost
  apply iInf_le_of_le (empiricalDistribution (fun i => (X i, Y i)))
  apply iInf_le_of_le (empirical_coupling hn X Y)
  exact le_of_eq (empirical_lintegral _ _)

#print axioms transportCost_le_empirical_cost
#print axioms empirical_coupling
#print axioms empirical_probability
#print axioms empirical_map
#print axioms empirical_lintegral
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma couplingValueSet_diagonal {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (hn : 0 < n) (ξ : Fin n → Z)
    (c : Z → Z → ENNReal) (hc0 : ∀ z, c z z = 0) (l : Z → ℝ) :
    ∃ L : ℝ, (0, L) ∈ couplingValueSet (empiricalDistribution ξ)
      (fun z => c z.1 z.2) (fun z => ENNReal.ofReal (l z.1)) := by
  let π := empiricalDistribution (fun i => (ξ i, ξ i))
  have hcost : (∫⁻ z, c z.1 z.2 ∂π) = 0 := by
    rw [empirical_lintegral]
    simp [hc0]
  have hloss : (∫⁻ z, ENNReal.ofReal (l z.1) ∂π) ≠ ⊤ := by
    rw [empirical_lintegral]
    apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne')
    · exact ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.ofReal_ne_top)
  refine ⟨(∫⁻ z, ENNReal.ofReal (l z.1) ∂π).toReal, π,
    empirical_probability hn _, empirical_map _ Prod.snd measurable_snd, ?_, hloss, ?_⟩
  · rw [hcost]
    simp
  · rw [hcost, ENNReal.toReal_zero]

lemma empirical_coupling_support {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (hn : 0 < n) (ξ : Fin n → Z)
    (c : Z → Z → ENNReal) (hc0 : ∀ z, c z z = 0) (l : Z → ℝ)
    (hl : Measurable (fun z => ENNReal.ofReal (l z))) (δ : ℝ) (hδ : 0 < δ)
    (hfinite : worstCase c δ (empiricalDistribution ξ) l ≠ ⊤) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ π : Measure (Z × Z), IsProbabilityMeasure π →
      π.map Prod.snd = empiricalDistribution ξ → (∫⁻ z, c z.1 z.2 ∂π) ≠ ⊤ →
      (∫⁻ z, ENNReal.ofReal (l z.1) ∂π) ≠ ⊤ →
      (∫⁻ z, ENNReal.ofReal (l z.1) ∂π).toReal ≤
        (worstCase c δ (empiricalDistribution ξ) l).toReal +
          γ * ((∫⁻ z, c z.1 z.2 ∂π).toReal - δ) := by
  obtain ⟨L, hL⟩ := couplingValueSet_diagonal hn ξ c hc0 l
  obtain ⟨γ, hγ, hbound⟩ := supporting_multiplier _
    (couplingValueSet_convex (empiricalDistribution ξ) _ _) δ _ L hδ hL
    (couplingValueSet_budget (empiricalDistribution ξ) c l hl δ hfinite)
  refine ⟨γ, hγ, ?_⟩
  intro π hπ hs hcost hloss
  exact hbound _ ⟨π, hπ, hs, hcost, hloss, rfl⟩

#print axioms couplingValueSet_diagonal
#print axioms empirical_coupling_support
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma empirical_integral_ne_top {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (hn : 0 < n) (ξ : Fin n → Z)
    (f : Z → ENNReal) (hf : ∀ i, f (ξ i) ≠ ⊤) :
    (∫⁻ z, f z ∂empiricalDistribution ξ) ≠ ⊤ := by
  rw [empirical_lintegral]
  exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne'))
    (ENNReal.sum_ne_top.mpr (fun i _ => hf i))

lemma empirical_integral_toReal {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (ξ : Fin n → Z)
    (f : Z → ENNReal) (hf : ∀ i, f (ξ i) ≠ ⊤) :
    (∫⁻ z, f z ∂empiricalDistribution ξ).toReal =
      (n : ℝ)⁻¹ * ∑ i, (f (ξ i)).toReal := by
  rw [empirical_lintegral, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_sum (fun i _ => hf i)]

lemma sample_support_bound {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (hn : 0 < n) (ξ : Fin n → Z)
    (c : Z → Z → ENNReal) (l : Z → ℝ) (hl0 : ∀ z, 0 ≤ l z)
    (δ γ V : ℝ)
    (hsupport : ∀ π : Measure (Z × Z), IsProbabilityMeasure π →
      π.map Prod.snd = empiricalDistribution ξ → (∫⁻ z, c z.1 z.2 ∂π) ≠ ⊤ →
      (∫⁻ z, ENNReal.ofReal (l z.1) ∂π) ≠ ⊤ →
      (∫⁻ z, ENNReal.ofReal (l z.1) ∂π).toReal ≤
        V + γ * ((∫⁻ z, c z.1 z.2 ∂π).toReal - δ))
    (u : Fin n → Z) (hu : ∀ i, c (u i) (ξ i) ≠ ⊤) :
    γ * δ + (n : ℝ)⁻¹ * ∑ i, (l (u i) - γ * (c (u i) (ξ i)).toReal) ≤ V := by
  have hπ := empirical_coupling hn u ξ
  have hc := empirical_integral_ne_top hn (fun i => (u i, ξ i)) (fun z => c z.1 z.2) hu
  have hl := empirical_integral_ne_top hn (fun i => (u i, ξ i))
    (fun z => ENNReal.ofReal (l z.1)) (fun i => ENNReal.ofReal_ne_top)
  have he := hsupport _ hπ.1 hπ.2.2 hc hl
  rw [empirical_integral_toReal (fun i => (u i, ξ i)) (fun z => c z.1 z.2) hu,
    empirical_integral_toReal (fun i => (u i, ξ i)) (fun z => ENNReal.ofReal (l z.1))
      (fun i => ENNReal.ofReal_ne_top)] at he
  simp only [ENNReal.toReal_ofReal (hl0 _)] at he
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  nlinarith

#print axioms empirical_integral_ne_top
#print axioms empirical_integral_toReal
#print axioms sample_support_bound
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open scoped BigOperators

lemma sum_iSup_independent {ι : Type*} [Fintype ι] {α : ι → Type*}
    (default : ∀ i, α i) (f : ∀ i, α i → ENNReal) :
    (∑ i, ⨆ x : α i, f i x) = ⨆ x : ∀ i, α i, ∑ i, f i (x i) := by
  classical
  have he (i : ι) : (⨆ u : α i, f i u) = ⨆ x : ∀ i, α i, f i (x i) := by
    apply le_antisymm
    · refine iSup_le fun u => ?_
      apply le_iSup_of_le (Function.update default i u)
      simp
    · exact iSup_le fun x => le_iSup (f i) (x i)
  simp_rw [he]
  apply ENNReal.finsetSum_iSup
  intro x y
  refine ⟨fun i => if f i (x i) ≤ f i (y i) then y i else x i, ?_⟩
  intro i
  dsimp only
  split_ifs with h
  · exact ⟨h, le_rfl⟩
  · exact ⟨le_rfl, le_of_lt (lt_of_not_ge h)⟩

#print axioms sum_iSup_independent
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open RWPI.SqrtLasso

lemma phi_eq_nonnegative_penalty_sup {Z : Type*} (c : Z → Z → ENNReal)
    (hc0 : ∀ z, c z z = 0) (l : Z → ℝ) (hl0 : ∀ z, 0 ≤ l z)
    (γ : ℝ) (hγ : 0 ≤ γ) (w : Z) :
    phi c l γ w =
      ⨆ u : {u : Z // c u w ≠ ⊤ ∧ 0 ≤ l u - γ * (c u w).toReal},
        ENNReal.ofReal (l u - γ * (c u w).toReal) := by
  have hterm (u : Z) (hu : c u w ≠ ⊤) :
      ENNReal.ofReal (l u) - ENNReal.ofReal γ * c u w =
        ENNReal.ofReal (l u - γ * (c u w).toReal) := by
    rw [ENNReal.ofReal_sub _ (mul_nonneg hγ ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul hγ, ENNReal.ofReal_toReal hu]
  unfold phi
  apply le_antisymm
  · refine iSup_le fun u => iSup_le fun hu => ?_
    rw [hterm u hu]
    by_cases hpos : 0 ≤ l u - γ * (c u w).toReal
    · exact le_iSup_of_le ⟨u, hu, hpos⟩ le_rfl
    · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hpos)]
      exact bot_le
  · refine iSup_le fun u => ?_
    apply le_iSup_of_le (u : Z)
    apply le_iSup_of_le u.property.1
    rw [hterm _ u.property.1]

lemma baseline_nonnegative_penalty {Z : Type*} (c : Z → Z → ENNReal)
    (hc0 : ∀ z, c z z = 0) (l : Z → ℝ) (hl0 : ∀ z, 0 ≤ l z)
    (γ : ℝ) (w : Z) : c w w ≠ ⊤ ∧ 0 ≤ l w - γ * (c w w).toReal := by
  simp [hc0, hl0]

#print axioms phi_eq_nonnegative_penalty_sup
#print axioms baseline_nonnegative_penalty
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma dual_upper_of_support {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (hn : 0 < n) (ξ : Fin n → Z)
    (c : Z → Z → ENNReal) (hc0 : ∀ z, c z z = 0) (l : Z → ℝ) (hl0 : ∀ z, 0 ≤ l z)
    (δ γ V : ℝ) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hsupport : ∀ π : Measure (Z × Z), IsProbabilityMeasure π →
      π.map Prod.snd = empiricalDistribution ξ → (∫⁻ z, c z.1 z.2 ∂π) ≠ ⊤ →
      (∫⁻ z, ENNReal.ofReal (l z.1) ∂π) ≠ ⊤ →
      (∫⁻ z, ENNReal.ofReal (l z.1) ∂π).toReal ≤
        V + γ * ((∫⁻ z, c z.1 z.2 ∂π).toReal - δ)) :
    ENNReal.ofReal (γ * δ) + (n : ENNReal)⁻¹ * ∑ i, phi c l γ (ξ i) ≤ ENNReal.ofReal V := by
  let α : Fin n → Type _ := fun i =>
    {u : Z // c u (ξ i) ≠ ⊤ ∧ 0 ≤ l u - γ * (c u (ξ i)).toReal}
  let base : ∀ i, α i := fun i => ⟨ξ i, baseline_nonnegative_penalty c hc0 l hl0 γ (ξ i)⟩
  let F : ∀ i, α i → ENNReal := fun i u => ENNReal.ofReal (l u - γ * (c u (ξ i)).toReal)
  have hs (i : Fin n) : phi c l γ (ξ i) = ⨆ u : α i, F i u :=
    phi_eq_nonnegative_penalty_sup c hc0 l hl0 γ hγ (ξ i)
  have hsum : (∑ i, phi c l γ (ξ i)) = ⨆ u : ∀ i, α i, ∑ i, F i (u i) := by
    simp_rw [hs]
    exact sum_iSup_independent base F
  letI : Nonempty (∀ i, α i) := ⟨base⟩
  rw [hsum, ENNReal.mul_iSup, ENNReal.add_iSup]
  refine iSup_le fun u => ?_
  let r : Fin n → ℝ := fun i => l (u i) - γ * (c (u i) (ξ i)).toReal
  have hr : ∀ i, 0 ≤ r i := fun i => (u i).property.2
  have hreal := sample_support_bound hn ξ c l hl0 δ γ V hsupport
    (fun i => (u i : Z)) (fun i => (u i).property.1)
  have hmean : 0 ≤ (n : ℝ)⁻¹ * ∑ i, r i :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hr i))
  have he : (n : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (r i) =
      ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i, r i) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ)⁻¹),
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => hr i)]
  change ENNReal.ofReal (γ * δ) + (n : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (r i) ≤ _
  rw [he, ← ENNReal.ofReal_add (mul_nonneg hγ hδ) hmean]
  exact ENNReal.ofReal_le_ofReal hreal

#print axioms dual_upper_of_support
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory

lemma transport_infimum_bound {Z : Type*} [MeasurableSpace Z]
    (c : Z → Z → ENNReal) (P Q : Measure Z) (a κ C : ENNReal)
    (hκ0 : κ ≠ 0) (hκtop : κ ≠ ⊤)
    (h : ∀ π : Measure (Z × Z),
      IsProbabilityMeasure π ∧ π.map Prod.fst = P ∧ π.map Prod.snd = Q →
      a ≤ κ * (∫⁻ z, c z.1 z.2 ∂π) + C) :
    a ≤ κ * RWPI.SqrtLasso.transportCost c P Q + C := by
  unfold RWPI.SqrtLasso.transportCost
  rw [ENNReal.mul_iInf_of_ne hκ0 hκtop, ENNReal.iInf_add]
  refine le_iInf fun π => ?_
  rw [ENNReal.mul_iInf_of_ne hκ0 hκtop, ENNReal.iInf_add]
  exact le_iInf fun hc => h π hc

lemma worstCase_upper_of_coupling_bound {Z : Type*} [MeasurableSpace Z]
    (c : Z → Z → ENNReal) (Q : Measure Z) (l : Z → ℝ) (δ : ℝ) (κ C : ENNReal)
    (hκ0 : κ ≠ 0) (hκtop : κ ≠ ⊤)
    (h : ∀ P : Measure Z, IsProbabilityMeasure P → ∀ π : Measure (Z × Z),
      IsProbabilityMeasure π ∧ π.map Prod.fst = P ∧ π.map Prod.snd = Q →
      (∫⁻ z, ENNReal.ofReal (l z) ∂P) ≤ κ * (∫⁻ z, c z.1 z.2 ∂π) + C) :
    RWPI.SqrtLasso.worstCase c δ Q l ≤ κ * ENNReal.ofReal δ + C := by
  unfold RWPI.SqrtLasso.worstCase
  refine iSup_le fun P => iSup_le fun hP => ?_
  apply le_trans (transport_infimum_bound c P Q _ κ C hκ0 hκtop (h P hP.1))
  gcongr
  exact hP.2

#print axioms transport_infimum_bound
#print axioms worstCase_upper_of_coupling_bound
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open RWPI.SqrtLasso

lemma phi_pointwise_upper {Z : Type*} (c : Z → Z → ENNReal) (l : Z → ℝ)
    (γ : ℝ) (hγ : 0 < γ) (z w : Z) :
    ENNReal.ofReal (l z) ≤ ENNReal.ofReal γ * c z w + phi c l γ w := by
  by_cases hc : c z w = ⊤
  · have hg : ENNReal.ofReal γ ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hγ)
    simp [hc, hg]
  · have hs : ENNReal.ofReal (l z) - ENNReal.ofReal γ * c z w ≤ phi c l γ w :=
      le_iSup_of_le z (le_iSup_of_le hc le_rfl)
    calc
      _ ≤ (ENNReal.ofReal (l z) - ENNReal.ofReal γ * c z w) + ENNReal.ofReal γ * c z w := le_tsub_add
      _ ≤ phi c l γ w + ENNReal.ofReal γ * c z w := add_le_add hs le_rfl
      _ = _ := add_comm _ _

lemma weak_duality_of_measurable_majorant {Z : Type*} [MeasurableSpace Z]
    (c : Z → Z → ENNReal) (l : Z → ℝ)
    (hl : Measurable (fun z => ENNReal.ofReal (l z)))
    (Q : Measure Z) (δ γ : ℝ) (hγ : 0 < γ)
    (g : Z → ENNReal) (hg : Measurable g) (hmajor : ∀ w, phi c l γ w ≤ g w) :
    worstCase c δ Q l ≤ ENNReal.ofReal γ * ENNReal.ofReal δ + ∫⁻ w, g w ∂Q := by
  apply worstCase_upper_of_coupling_bound c Q l δ (ENNReal.ofReal γ) _
    (ne_of_gt (ENNReal.ofReal_pos.mpr hγ)) ENNReal.ofReal_ne_top
  intro P _ π hπ
  rw [← hπ.2.1, ← hπ.2.2, lintegral_map hl measurable_fst, lintegral_map hg measurable_snd]
  apply le_trans (lintegral_mono (fun z : Z × Z =>
    (phi_pointwise_upper c l γ hγ z.1 z.2).trans
      (add_le_add le_rfl (hmajor z.2))))
  have hgs : Measurable (fun z : Z × Z => g z.2) := hg.comp measurable_snd
  rw [lintegral_add_right (fun z : Z × Z => ENNReal.ofReal γ * c z.1 z.2)
    hgs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

#print axioms phi_pointwise_upper
#print axioms weak_duality_of_measurable_majorant
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma empirical_weak_duality_positive {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (ξ : Fin n → Z)
    (c : Z → Z → ENNReal) (l : Z → ℝ)
    (hl : Measurable (fun z => ENNReal.ofReal (l z))) (δ γ : ℝ) (hγ : 0 < γ) :
    worstCase c δ (empiricalDistribution ξ) l ≤
      ENNReal.ofReal γ * ENNReal.ofReal δ + (n : ENNReal)⁻¹ * ∑ i, phi c l γ (ξ i) := by
  classical
  let g : Z → ENNReal := fun w => ⨅ i : Fin n, if w = ξ i then phi c l γ (ξ i) else ⊤
  have hg : Measurable g := by
    apply Measurable.iInf
    intro i
    exact Measurable.ite (measurableSet_singleton (ξ i)) measurable_const measurable_const
  have hmajor : ∀ w, phi c l γ w ≤ g w := by
    intro w
    apply le_iInf
    intro i
    split_ifs with he
    · rw [he]
    · exact le_top
  have he (i : Fin n) : g (ξ i) = phi c l γ (ξ i) := by
    apply le_antisymm
    · apply (iInf_le _ i).trans
      simp
    · exact hmajor _
  have h := weak_duality_of_measurable_majorant c l hl (empiricalDistribution ξ) δ γ hγ g hg hmajor
  rw [empirical_lintegral] at h
  simp_rw [he] at h
  exact h

#print axioms empirical_weak_duality_positive
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma phi_le_zero_multiplier {Z : Type*} (c : Z → Z → ENNReal) (l : Z → ℝ)
    (γ : ℝ) (w : Z) : phi c l γ w ≤ phi c l 0 w := by
  unfold phi
  refine iSup_le fun u => iSup_le fun hc => ?_
  apply le_iSup_of_le u
  apply le_iSup_of_le hc
  simp only [ENNReal.ofReal_zero, zero_mul, tsub_zero]
  exact tsub_le_self

lemma ennreal_le_of_positive_linear_bounds (a C : ENNReal) (δ : ℝ) (hδ : 0 ≤ δ)
    (hupper : ∀ γ : ℝ, 0 < γ → a ≤ ENNReal.ofReal γ * ENNReal.ofReal δ + C) : a ≤ C := by
  by_cases hC : C = ⊤
  · simp [hC]
  · have ha : a ≠ ⊤ := ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hC⟩)
      (by simpa using hupper 1 zero_lt_one)
    by_contra hle
    have hgap : 0 < a.toReal - C.toReal := sub_pos.mpr
      ((ENNReal.toReal_lt_toReal hC ha).mpr (lt_of_not_ge hle))
    obtain ⟨γ, hγ, hsmall⟩ := exists_pos_mul_lt hgap δ
    have he : ENNReal.ofReal γ * ENNReal.ofReal δ + C =
        ENNReal.ofReal (γ * δ + C.toReal) := by
      calc
        _ = ENNReal.ofReal (γ * δ) + ENNReal.ofReal C.toReal := by
          rw [ENNReal.ofReal_mul hγ.le, ENNReal.ofReal_toReal hC]
        _ = _ := (ENNReal.ofReal_add (mul_nonneg hγ.le hδ) ENNReal.toReal_nonneg).symm
    have hu := hupper γ hγ
    rw [he] at hu
    have ht := (ENNReal.le_ofReal_iff_toReal_le ha
      (add_nonneg (mul_nonneg hγ.le hδ) ENNReal.toReal_nonneg)).mp hu
    nlinarith

lemma empirical_weak_duality {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (ξ : Fin n → Z)
    (c : Z → Z → ENNReal) (l : Z → ℝ)
    (hl : Measurable (fun z => ENNReal.ofReal (l z))) (δ : ℝ) (hδ : 0 ≤ δ)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    worstCase c δ (empiricalDistribution ξ) l ≤
      ENNReal.ofReal (γ * δ) + (n : ENNReal)⁻¹ * ∑ i, phi c l γ (ξ i) := by
  by_cases hγpos : 0 < γ
  · simpa only [ENNReal.ofReal_mul hγ] using
      empirical_weak_duality_positive ξ c l hl δ γ hγpos
  · have hz : γ = 0 := le_antisymm (le_of_not_gt hγpos) hγ
    subst γ
    simp only [zero_mul, ENNReal.ofReal_zero, zero_add]
    apply ennreal_le_of_positive_linear_bounds _ _ δ hδ
    intro γ hγpos
    apply (empirical_weak_duality_positive ξ c l hl δ γ hγpos).trans
    apply add_le_add le_rfl
    gcongr with i
    exact phi_le_zero_multiplier c l γ (ξ i)

#print axioms phi_le_zero_multiplier
#print axioms ennreal_le_of_positive_linear_bounds
#print axioms empirical_weak_duality
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma empirical_strong_duality {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (hn : 0 < n) (ξ : Fin n → Z)
    (c : Z → Z → ENNReal) (hc0 : ∀ z, c z z = 0) (l : Z → ℝ)
    (hl : Measurable (fun z => ENNReal.ofReal (l z))) (hl0 : ∀ z, 0 ≤ l z)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 ≤ γ ∧
      worstCase c δ (empiricalDistribution ξ) l =
        ENNReal.ofReal (γ * δ) + (n : ENNReal)⁻¹ * ∑ i, phi c l γ (ξ i) ∧
      ∀ γ' : ℝ, 0 ≤ γ' → worstCase c δ (empiricalDistribution ξ) l ≤
        ENNReal.ofReal (γ' * δ) + (n : ENNReal)⁻¹ * ∑ i, phi c l γ' (ξ i) := by
  have hweak := empirical_weak_duality ξ c l hl δ hδ.le
  by_cases htop : worstCase c δ (empiricalDistribution ξ) l = ⊤
  · refine ⟨0, le_rfl, le_antisymm (hweak 0 le_rfl) ?_, hweak⟩
    rw [htop]
    exact le_top
  · obtain ⟨γ, hγ, hs⟩ := empirical_coupling_support hn ξ c hc0 l hl δ hδ htop
    have hu := dual_upper_of_support hn ξ c hc0 l hl0 δ γ
      (worstCase c δ (empiricalDistribution ξ) l).toReal hδ.le hγ hs
    rw [ENNReal.ofReal_toReal htop] at hu
    exact ⟨γ, hγ, le_antisymm (hweak γ hγ) hu, hweak⟩

#print axioms empirical_strong_duality
end TransportCodex

set_option autoImplicit false
open MeasureTheory RWPI.SqrtLasso
open scoped BigOperators

theorem solution {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (c : (Fin d → ℝ) × ℝ → (Fin d → ℝ) × ℝ → ENNReal)
    (hc : LowerSemicontinuous (Function.uncurry c)) (hc0 : ∀ z, c z z = 0)
    (l : (Fin d → ℝ) × ℝ → ℝ) (hl : UpperSemicontinuous l) (hl0 : ∀ z, 0 ≤ l z)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 ≤ γ ∧
      worstCase c δ (WassersteinDRO.Regularization.empiricalDistribution
          (fun i : Fin n => (X i, Y i))) l =
        ENNReal.ofReal (γ * δ) + (n : ENNReal)⁻¹ * ∑ i, phi c l γ (X i, Y i) ∧
      ∀ γ' : ℝ, 0 ≤ γ' →
        worstCase c δ (WassersteinDRO.Regularization.empiricalDistribution
            (fun i : Fin n => (X i, Y i))) l ≤
          ENNReal.ofReal (γ' * δ) + (n : ENNReal)⁻¹ * ∑ i, phi c l γ' (X i, Y i) := by
  exact TransportCodex.empirical_strong_duality hn (fun i => (X i, Y i)) c hc0 l
    (ENNReal.measurable_ofReal.comp hl.measurable) hl0 δ hδ

#print axioms solution
