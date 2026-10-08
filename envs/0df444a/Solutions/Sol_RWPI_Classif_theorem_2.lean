-- Prove2me | solution 1 for RWPI.Classif.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T11:49:43.701373+00:00
-- url     : https://prove2.me/submissions/505563a3-50a1-4701-87c6-32f58db20f14

import Definitions.Def_RWPI_Classif_losses
import Definitions.Def_RWPI_SqrtLasso_Nq
import Definitions.Def_RWPI_SqrtLasso_phi
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_RWPI_SqrtLasso_worstCase
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Mathlib

-- Complete local proof: Solutions.Classif_PhiFiber
set_option autoImplicit false
namespace ClassifCodex
lemma guarded_phi_fiber {d : ℕ} (q : ENNReal) (l : ((Fin d → ℝ) × ℝ) → ℝ)
    (lam : ℝ) (x₀ : Fin d → ℝ) (y : ℝ) :
    RWPI.SqrtLasso.phi (RWPI.SqrtLasso.Nq q) l lam (x₀,y) =
      ⨆ x : Fin d → ℝ, ENNReal.ofReal (l (x,y)) -
        ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x-x₀)‖ := by
  unfold RWPI.SqrtLasso.phi
  apply le_antisymm
  · apply iSup_le
    rintro ⟨x,u⟩
    apply iSup_le
    intro hc
    have hu : u = y := by
      by_contra h
      simp only [RWPI.SqrtLasso.Nq, if_neg h] at hc
      exact hc rfl
    subst u
    simp only [RWPI.SqrtLasso.Nq, if_pos rfl]
    exact le_iSup (fun x : Fin d → ℝ => ENNReal.ofReal (l (x,y)) -
      ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x-x₀)‖) x
  · apply iSup_le
    intro x
    apply le_iSup_of_le (x,y)
    have hc : RWPI.SqrtLasso.Nq q (x,y) (x₀,y) ≠ ⊤ := by
      simp [RWPI.SqrtLasso.Nq]
    apply le_iSup_of_le hc
    simp [RWPI.SqrtLasso.Nq]
#print axioms guarded_phi_fiber
end ClassifCodex

-- Complete local proof: Solutions.Classif_OuterThreshold
set_option autoImplicit false
open scoped BigOperators
namespace ClassifCodex

lemma ennreal_average {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (n : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (a i) =
      ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, a i) := by
  rw [one_div, ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ)⁻¹),
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i)]

lemma outer_threshold_min {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 ≤ δ) :
    (⨅ (lam : ℝ) (_ : 0 ≤ lam), ENNReal.ofReal (δ * lam) + (n : ENNReal)⁻¹ *
      ∑ i, if B ≤ lam then ENNReal.ofReal (a i) else ⊤) =
        ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, a i + δ * B) := by
  have hA : 0 ≤ (1 / (n : ℝ)) * ∑ i, a i :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => ha i))
  apply le_antisymm
  · apply iInf_le_of_le B
    apply iInf_le_of_le hB
    simp only [if_pos le_rfl]
    rw [ennreal_average hn a ha, ← ENNReal.ofReal_add (mul_nonneg hδ hB) hA]
    simp only [add_comm, le_refl]
  · apply le_iInf
    intro lam
    apply le_iInf
    intro hlam
    by_cases h : B ≤ lam
    · simp only [if_pos h]
      rw [ennreal_average hn a ha, ← ENNReal.ofReal_add (mul_nonneg hδ hlam) hA]
      apply ENNReal.ofReal_le_ofReal
      nlinarith
    · have hs : (∑ i : Fin n, if B ≤ lam then ENNReal.ofReal (a i) else ⊤) = ⊤ := by
        apply top_unique
        have he : (⊤ : ENNReal) ≤ ∑ i : Fin n, if B ≤ lam then ENNReal.ofReal (a i) else ⊤ := by
          have hk := Finset.single_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) =>
            (bot_le : 0 ≤ if B ≤ lam then ENNReal.ofReal (a i) else ⊤))
            (Finset.mem_univ (⟨0, hn⟩ : Fin n))
          simpa only [if_neg h] using hk
        exact he
      rw [hs, ENNReal.mul_top (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n))]
      simp

#print axioms ennreal_average
#print axioms outer_threshold_min
end ClassifCodex

-- Complete local proof: Theorems.Thm_RWPI_SqrtLasso_proposition_1

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport

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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
namespace ClassifAcceptedTransport
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
end ClassifAcceptedTransport

set_option autoImplicit false
open MeasureTheory RWPI.SqrtLasso
open scoped BigOperators

theorem RWPI.SqrtLasso.proposition_1 {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
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
  exact ClassifAcceptedTransport.empirical_strong_duality hn (fun i => (X i, Y i)) c hc0 l
    (ENNReal.measurable_ofReal.comp hl.measurable) hl0 δ hδ

#print axioms RWPI.SqrtLasso.proposition_1

-- Complete local proof: Solutions.Classif_RiskEnvelope
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace ClassifCodex
lemma risk_from_inner {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (q : ENNReal) (hq : 1 ≤ q) (l : ((Fin d → ℝ) × ℝ) → ℝ)
    (hl : Measurable (fun z => ENNReal.ofReal (l z))) (hl0 : ∀ z, 0 ≤ l z)
    (B : ℝ) (hB : 0 ≤ B)
    (hinner : ∀ i (lam : ℝ), 0 ≤ lam →
      (⨆ x : Fin d → ℝ, ENNReal.ofReal (l (x,Y i)) -
        ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x-X i)‖) =
        if B ≤ lam then ENNReal.ofReal (l (X i,Y i)) else ⊤)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    RWPI.SqrtLasso.worstCase (RWPI.SqrtLasso.Nq q) δ
      (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i,Y i))) l =
      ENNReal.ofReal ((1/(n:ℝ))*∑ i, l (X i,Y i) + δ*B) := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  have hc0 : ∀ z : ((Fin d → ℝ) × ℝ), RWPI.SqrtLasso.Nq q z z = 0 := by
    intro z
    simp [RWPI.SqrtLasso.Nq]
  have hphi (i : Fin n) (lam : ℝ) (hlam : 0 ≤ lam) :
      RWPI.SqrtLasso.phi (RWPI.SqrtLasso.Nq q) l lam (X i,Y i) =
        if B ≤ lam then ENNReal.ofReal (l (X i,Y i)) else ⊤ := by
    rw [guarded_phi_fiber]
    exact hinner i lam hlam
  have hA : 0 ≤ (1/(n:ℝ))*∑ i, l (X i,Y i) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hl0 _))
  apply le_antisymm
  · have hu := ClassifAcceptedTransport.empirical_weak_duality (fun i => (X i,Y i))
      (RWPI.SqrtLasso.Nq q) l hl δ hδ B hB
    simp_rw [hphi _ B hB, if_pos le_rfl] at hu
    rw [ennreal_average hn _ (fun i => hl0 _),
      ← ENNReal.ofReal_add (mul_nonneg hB hδ) hA] at hu
    simpa only [add_comm, mul_comm] using hu
  · by_cases hpos : 0 < δ
    · obtain ⟨lam, hlam, he, _⟩ := ClassifAcceptedTransport.empirical_strong_duality hn
        (fun i => (X i,Y i)) (RWPI.SqrtLasso.Nq q) hc0 l hl hl0 δ hpos
      rw [he]
      simp_rw [hphi _ lam hlam]
      have hmin := outer_threshold_min hn (fun i => l (X i,Y i))
        (fun i => hl0 _) B δ hB hδ
      rw [← hmin]
      simpa only [mul_comm] using
        (iInf_le_of_le lam (iInf_le_of_le hlam le_rfl) :
          (⨅ (r : ℝ) (_ : 0 ≤ r), ENNReal.ofReal (δ*r) + (n:ENNReal)⁻¹ *
            ∑ i, if B ≤ r then ENNReal.ofReal (l (X i,Y i)) else ⊤) ≤
          ENNReal.ofReal (δ*lam) + (n:ENNReal)⁻¹ *
            ∑ i, if B ≤ lam then ENNReal.ofReal (l (X i,Y i)) else ⊤)
    · have hz : δ = 0 := le_antisymm (le_of_not_gt hpos) hδ
      subst δ
      simp only [zero_mul, add_zero]
      have hc := ClassifAcceptedTransport.transportCost_le_empirical_cost hn
        (fun i => (X i,Y i)) (fun i => (X i,Y i)) (RWPI.SqrtLasso.Nq q)
      simp only [hc0, Finset.sum_const_zero, mul_zero] at hc
      have hb : (∫⁻ z, ENNReal.ofReal (l z) ∂
          WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i,Y i))) ≤
          RWPI.SqrtLasso.worstCase (RWPI.SqrtLasso.Nq q) 0
            (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i,Y i))) l := by
        unfold RWPI.SqrtLasso.worstCase
        exact le_iSup_of_le _ (le_iSup_of_le
          ⟨ClassifAcceptedTransport.empirical_probability hn _, by simpa using hc⟩ le_rfl)
      rw [ClassifAcceptedTransport.empirical_lintegral, ennreal_average hn _ (fun i => hl0 _)] at hb
      exact hb
#print axioms risk_from_inner
end ClassifCodex

-- Complete local proof: Solutions.Classif_Holder
set_option autoImplicit false
namespace ClassifNorm
open scoped BigOperators

lemma holder_toReal (p q : ENNReal) (hpq : p.HolderConjugate q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) : p.toReal.HolderConjugate q.toReal := by
  have : p.HolderConjugate q := hpq
  refine ⟨?_, ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp,
    ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q p) hq⟩
  have h := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one p q)
  simpa [ENNReal.toReal_add, ENNReal.inv_ne_top,
    ENNReal.HolderConjugate.ne_zero p q, ENNReal.HolderConjugate.ne_zero q p] using h

lemma dot_abs_le_finite {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (x y : Fin d → ℝ) :
    |∑ j, x j * y j| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  rw [PiLp.norm_eq_sum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp),
    PiLp.norm_eq_sum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q p) hq)]
  calc
    |∑ j, x j * y j| ≤ ∑ j, |x j| * |y j| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => x j * y j) Finset.univ
    _ ≤ _ := by
      simpa using Real.inner_le_Lp_mul_Lq Finset.univ (fun j => |x j|)
        (fun j => |y j|) (holder_toReal p q hpq hp hq)

lemma dot_abs_le_one_top {d : ℕ} (x y : Fin d → ℝ) :
    |∑ j, x j * y j| ≤ ‖WithLp.toLp 1 x‖ * ‖WithLp.toLp ⊤ y‖ := by
  calc
    |∑ j, x j * y j| ≤ ∑ j, |x j| * |y j| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => x j * y j) Finset.univ
    _ ≤ ∑ j, |x j| * ‖WithLp.toLp ⊤ y‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa using PiLp.norm_apply_le (WithLp.toLp ⊤ y) j
    _ = _ := by
      rw [← Finset.sum_mul, PiLp.norm_eq_of_L1]
      simp

lemma dot_abs_le {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (x y : Fin d → ℝ) :
    |∑ j, x j * y j| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ := by
  have : p.HolderConjugate q := hpq
  by_cases hqt : q = ⊤
  · subst q
    have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).mp rfl
    subst p
    exact dot_abs_le_one_top x y
  · exact dot_abs_le_finite p q hpq
      ((ENNReal.HolderConjugate.ne_top_iff_ne_one p q).mpr hq.ne') hqt x y

#print axioms dot_abs_le_one_top
#print axioms dot_abs_le
#print axioms holder_toReal
#print axioms dot_abs_le_finite
end ClassifNorm

-- Complete local proof: Solutions.Classif_Norming
set_option autoImplicit false
namespace ClassifNorm
open scoped BigOperators NNReal

lemma norming_finite {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let f : Fin d → ℝ≥0 := fun j => ⟨|x j|, abs_nonneg _⟩
  have hc := holder_toReal p q hpq hp hq
  obtain ⟨g, hg, he⟩ := (NNReal.isGreatest_Lp Finset.univ f hc).1
  let y : Fin d → ℝ := fun j => if 0 ≤ x j then (g j : ℝ) else -(g j : ℝ)
  have hy (j : Fin d) : |y j| = (g j : ℝ) := by
    dsimp [y]
    split_ifs <;> simp
  have hxy (j : Fin d) : x j * y j = |x j| * (g j : ℝ) := by
    dsimp [y]
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  refine ⟨y, ?_, ?_⟩
  · rw [PiLp.norm_eq_sum hc.symm.pos]
    simp only [Real.norm_eq_abs, hy]
    have hbound := NNReal.rpow_le_one hg (one_div_nonneg.mpr hc.symm.nonneg)
    exact_mod_cast hbound
  · rw [PiLp.norm_eq_sum hc.pos]
    simp only [Real.norm_eq_abs]
    simp_rw [hxy]
    have heR := congrArg (fun z : ℝ≥0 => (z : ℝ)) he
    have hf (j : Fin d) : (f j : ℝ) = |x j| := rfl
    simpa only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_rpow, hf] using heR

lemma norming_one_top {d : ℕ} (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp ⊤ y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp 1 x‖ := by
  let y : Fin d → ℝ := fun j => if 0 ≤ x j then 1 else -1
  refine ⟨y, ?_, ?_⟩
  · rw [PiLp.norm_toLp]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro j
    dsimp [y]
    split_ifs <;> norm_num
  · rw [PiLp.norm_eq_of_L1]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [y]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]

lemma norming {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  have : p.HolderConjugate q := hpq
  by_cases hqt : q = ⊤
  · subst q
    have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).mp rfl
    subst p
    exact norming_one_top x
  · exact norming_finite p q hpq
      ((ENNReal.HolderConjugate.ne_top_iff_ne_one p q).mpr hq.ne') hqt x

lemma norming_unit_of_positive {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (x : Fin d → ℝ) (hx : 0 < ‖WithLp.toLp p x‖) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ = 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  obtain ⟨y, hy, hxy⟩ := norming p q hq hpq x
  refine ⟨y, le_antisymm hy ?_, hxy⟩
  have hbound := dot_abs_le p q hq hpq x y
  rw [hxy, abs_of_pos hx] at hbound
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hbound) hx

#print axioms norming_one_top
#print axioms norming
#print axioms norming_unit_of_positive
#print axioms norming_finite
end ClassifNorm

-- Complete local proof: Solutions.Classif_NormEndpoints
set_option autoImplicit false
open scoped BigOperators
namespace ClassifNorm

lemma dot_abs_le_all {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (x y : Fin d → ℝ) : |∑ j, x j * y j| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ := by
  have : p.HolderConjugate q := hpq
  by_cases hq1 : q = 1
  · subst q
    have hp : p = ⊤ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p 1).mpr rfl
    subst p
    have h := dot_abs_le_one_top y x
    simpa [mul_comm] using h
  · exact dot_abs_le p q (lt_of_le_of_ne (ENNReal.HolderConjugate.one_le q p) (Ne.symm hq1)) hpq x y

lemma norming_top_one {d : ℕ} (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp 1 y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp ⊤ x‖ := by
  classical
  cases isEmpty_or_nonempty (Fin d) with
  | inl hi =>
    have := hi
    have hx : x = 0 := by ext j; exact isEmptyElim j
    subst x
    refine ⟨0, ?_, ?_⟩ <;> simp
  | inr hi =>
    have := hi
    obtain ⟨j, hj⟩ := (IsGreatest.pi_norm x).1
    let y : Fin d → ℝ := fun i => if i = j then (if 0 ≤ x j then 1 else -1) else 0
    refine ⟨y, ?_, ?_⟩
    · rw [PiLp.norm_eq_of_L1]
      rw [Finset.sum_eq_single j]
      · by_cases hs : 0 ≤ x j <;> simp [y, hs]
      · intro i hi hij
        simp [y, hij]
      · simp
    · rw [PiLp.norm_toLp]
      have hj' : |x j| = ‖x‖ := by simpa [Real.norm_eq_abs] using hj
      by_cases hs : 0 ≤ x j
      · simpa [y, hs, abs_of_nonneg hs] using hj'
      · simpa [y, hs, abs_of_neg (lt_of_not_ge hs)] using hj'

lemma norming_all {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q) (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  have : p.HolderConjugate q := hpq
  by_cases hq1 : q = 1
  · subst q
    have hp : p = ⊤ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p 1).mpr rfl
    subst p
    exact norming_top_one x
  · exact norming p q (lt_of_le_of_ne (ENNReal.HolderConjugate.one_le q p) (Ne.symm hq1)) hpq x

lemma norming_unit_all_of_positive {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (x : Fin d → ℝ) (hx : 0 < ‖WithLp.toLp p x‖) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ = 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  obtain ⟨y, hy, hxy⟩ := norming_all p q hpq x
  refine ⟨y, le_antisymm hy ?_, hxy⟩
  have hbound := dot_abs_le_all p q hpq x y
  rw [hxy, abs_of_pos hx] at hbound
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hbound) hx

#print axioms dot_abs_le_all
#print axioms norming_top_one
#print axioms norming_all
#print axioms norming_unit_all_of_positive
end ClassifNorm

-- Complete local proof: Solutions.Classif_Softplus
set_option autoImplicit false
namespace ClassifCodex

noncomputable def softplus (u : ℝ) : ℝ := Real.log (1 + Real.exp u)

lemma softplus_nonnegative (u : ℝ) : 0 ≤ softplus u := by
  exact Real.log_nonneg (by linarith [Real.exp_pos u])

lemma le_softplus (u : ℝ) : u ≤ softplus u := by
  calc
    u = Real.log (Real.exp u) := (Real.log_exp u).symm
    _ ≤ Real.log (1 + Real.exp u) := Real.log_le_log (Real.exp_pos u) (by linarith)

lemma softplus_hasDerivAt (u : ℝ) :
    HasDerivAt softplus (Real.exp u / (1 + Real.exp u)) u := by
  change HasDerivAt (fun x : ℝ => Real.log (1 + Real.exp x))
    (Real.exp u / (1 + Real.exp u)) u
  exact ((Real.hasDerivAt_exp u).const_add 1).log (by positivity)

lemma softplus_lipschitz : LipschitzWith 1 softplus := by
  apply lipschitzWith_of_nnnorm_deriv_le (𝕜 := ℝ)
    (fun u => (softplus_hasDerivAt u).differentiableAt)
  intro u
  rw [(softplus_hasDerivAt u).deriv]
  have hpos : 0 ≤ Real.exp u / (1 + Real.exp u) := by positivity
  have hle : Real.exp u / (1 + Real.exp u) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hn : ‖Real.exp u / (1 + Real.exp u)‖ ≤ 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hpos]
  exact_mod_cast hn

#print axioms softplus_nonnegative
#print axioms le_softplus
#print axioms softplus_hasDerivAt
#print axioms softplus_lipschitz
end ClassifCodex

-- Complete local proof: Solutions.Classif_LossBounds
set_option autoImplicit false
open scoped BigOperators
namespace ClassifCodex

noncomputable def margin {d : ℕ} (β : Fin d → ℝ) (y : ℝ) (x : Fin d → ℝ) : ℝ :=
  -(y * (β ⬝ᵥ x))

lemma binary_abs (y : ℝ) (hy : y = 1 ∨ y = -1) : |y| = 1 := by
  rcases hy with rfl | rfl <;> norm_num

lemma margin_sub {d : ℕ} (β x x₀ : Fin d → ℝ) (y : ℝ) :
    margin β y x - margin β y x₀ = -y * (β ⬝ᵥ (x - x₀)) := by
  unfold margin
  rw [dotProduct_sub]
  ring

lemma margin_abs_sub_le {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x x₀ : Fin d → ℝ) (y : ℝ) (hy : y = 1 ∨ y = -1) :
    |margin β y x - margin β y x₀| ≤ ‖WithLp.toLp p β‖ * ‖WithLp.toLp q (x - x₀)‖ := by
  rw [margin_sub, abs_mul, abs_neg, binary_abs y hy, one_mul]
  exact ClassifNorm.dot_abs_le_all p q hpq β (x - x₀)

lemma hinge_scalar_lipschitz : LipschitzWith 1 (fun u : ℝ => max 0 (1 + u)) := by
  have ha : LipschitzWith 1 (fun u : ℝ => 1 + u) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq]
  simpa using (LipschitzWith.const (α := ℝ) (0 : ℝ)).max ha

lemma logLoss_nonnegative {d : ℕ} (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) :
    0 ≤ RWPI.Classif.logLoss β z := softplus_nonnegative _

lemma hingeLoss_nonnegative {d : ℕ} (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) :
    0 ≤ RWPI.Classif.hingeLoss β z := le_max_left _ _

lemma margin_le_logLoss {d : ℕ} (β x : Fin d → ℝ) (y : ℝ) :
    margin β y x ≤ RWPI.Classif.logLoss β (x, y) := le_softplus _

lemma margin_le_hingeLoss {d : ℕ} (β x : Fin d → ℝ) (y : ℝ) :
    margin β y x ≤ RWPI.Classif.hingeLoss β (x, y) := by
  have h := le_max_right (0 : ℝ) (1 + margin β y x)
  change margin β y x ≤ max 0 (1 + margin β y x)
  linarith

lemma logLoss_abs_sub_le {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x x₀ : Fin d → ℝ) (y : ℝ) (hy : y = 1 ∨ y = -1) :
    |RWPI.Classif.logLoss β (x, y) - RWPI.Classif.logLoss β (x₀, y)| ≤
      ‖WithLp.toLp p β‖ * ‖WithLp.toLp q (x - x₀)‖ := by
  have h := softplus_lipschitz.dist_le_mul (margin β y x) (margin β y x₀)
  have h' : |RWPI.Classif.logLoss β (x, y) - RWPI.Classif.logLoss β (x₀, y)| ≤
      |margin β y x - margin β y x₀| := by
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    change |RWPI.Classif.logLoss β (x, y) - RWPI.Classif.logLoss β (x₀, y)| ≤
      |margin β y x - margin β y x₀| at h
    exact h
  exact h'.trans (margin_abs_sub_le p q hpq β x x₀ y hy)

lemma hingeLoss_abs_sub_le {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x x₀ : Fin d → ℝ) (y : ℝ) (hy : y = 1 ∨ y = -1) :
    |RWPI.Classif.hingeLoss β (x, y) - RWPI.Classif.hingeLoss β (x₀, y)| ≤
      ‖WithLp.toLp p β‖ * ‖WithLp.toLp q (x - x₀)‖ := by
  have h := hinge_scalar_lipschitz.dist_le_mul (margin β y x) (margin β y x₀)
  have h' : |RWPI.Classif.hingeLoss β (x, y) - RWPI.Classif.hingeLoss β (x₀, y)| ≤
      |margin β y x - margin β y x₀| := by
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    change |RWPI.Classif.hingeLoss β (x, y) - RWPI.Classif.hingeLoss β (x₀, y)| ≤
      |margin β y x - margin β y x₀| at h
    exact h
  exact h'.trans (margin_abs_sub_le p q hpq β x x₀ y hy)

#print axioms binary_abs
#print axioms margin_sub
#print axioms margin_abs_sub_le
#print axioms hinge_scalar_lipschitz
#print axioms logLoss_nonnegative
#print axioms hingeLoss_nonnegative
#print axioms margin_le_logLoss
#print axioms margin_le_hingeLoss
#print axioms logLoss_abs_sub_le
#print axioms hingeLoss_abs_sub_le
end ClassifCodex

-- Complete local proof: Solutions.Classif_NormingRay
set_option autoImplicit false
namespace ClassifCodex

lemma margin_ray {d : ℕ} (β x₀ v : Fin d → ℝ) (y t B : ℝ)
    (hy : y = 1 ∨ y = -1) (hdot : β ⬝ᵥ v = B) :
    margin β y (x₀ - (t * y) • v) = margin β y x₀ + t * B := by
  unfold margin
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hdot]
  rcases hy with rfl | rfl <;> ring

lemma norming_ray_distance {d : ℕ} (q : ENNReal) (hq : 1 ≤ q)
    (x₀ v : Fin d → ℝ) (y t : ℝ) (hy : y = 1 ∨ y = -1) (ht : 0 ≤ t)
    (hv : ‖WithLp.toLp q v‖ = 1) :
    ‖WithLp.toLp q ((x₀ - (t * y) • v) - x₀)‖ = t := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  have he : (x₀ - (t * y) • v) - x₀ = (-(t * y)) • v := by module
  rw [he]
  change ‖(-(t * y)) • WithLp.toLp q v‖ = t
  rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_neg, abs_mul, binary_abs y hy,
    abs_of_nonneg ht, mul_one]

#print axioms margin_ray
#print axioms norming_ray_distance
end ClassifCodex

-- Complete local proof: Solutions.Classif_InnerEnvelope
set_option autoImplicit false
namespace ClassifCodex

lemma inner_envelope_eq_if {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x₀ : Fin d → ℝ) (y : ℝ) (hy : y = 1 ∨ y = -1)
    (l : (Fin d → ℝ) → ℝ)
    (hlip : ∀ x, |l x - l x₀| ≤ ‖WithLp.toLp p β‖ * ‖WithLp.toLp q (x - x₀)‖)
    (hlower : ∀ x, margin β y x ≤ l x) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ x : Fin d → ℝ, ENNReal.ofReal (l x) -
      ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x - x₀)‖) =
      if ‖WithLp.toLp p β‖ ≤ lam then ENNReal.ofReal (l x₀) else ⊤ := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have he (x : Fin d → ℝ) :
      ENNReal.ofReal (l x) - ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x - x₀)‖ =
        ENNReal.ofReal (l x - lam * ‖WithLp.toLp q (x - x₀)‖) := by
    rw [ENNReal.ofReal_sub _ (mul_nonneg hlam (norm_nonneg _)), ENNReal.ofReal_mul hlam]
  simp_rw [he]
  by_cases hB : ‖WithLp.toLp p β‖ ≤ lam
  · rw [if_pos hB]
    apply le_antisymm
    · apply iSup_le
      intro x
      apply ENNReal.ofReal_le_ofReal
      have h := (le_abs_self (l x - l x₀)).trans (hlip x)
      have hn := norm_nonneg (WithLp.toLp q (x - x₀))
      nlinarith
    · apply le_iSup_of_le x₀
      simp
  · rw [if_neg hB]
    have hgap : 0 < ‖WithLp.toLp p β‖ - lam := sub_pos.mpr (lt_of_not_ge hB)
    have hβ : 0 < ‖WithLp.toLp p β‖ := by linarith
    obtain ⟨v, hv, hdot⟩ := ClassifNorm.norming_unit_all_of_positive p q hpq β hβ
    apply iSup_eq_top.mpr
    intro r hr
    let a := margin β y x₀
    let t := max 0 ((r.toReal - a + 1) / (‖WithLp.toLp p β‖ - lam))
    have ht : 0 ≤ t := le_max_left _ _
    have htbound : (r.toReal - a + 1) / (‖WithLp.toLp p β‖ - lam) ≤ t := le_max_right _ _
    have hprod : r.toReal - a + 1 ≤ t * (‖WithLp.toLp p β‖ - lam) :=
      (div_le_iff₀ hgap).mp htbound
    let x := x₀ - (t * y) • v
    refine ⟨x, ?_⟩
    apply (ENNReal.lt_ofReal_iff_toReal_lt (ne_of_lt hr)).mpr
    have hnorm := norming_ray_distance q (ENNReal.HolderConjugate.one_le q p) x₀ v y t hy ht hv
    have hmargin := margin_ray β x₀ v y t ‖WithLp.toLp p β‖ hy hdot
    have hl := hlower x
    dsimp [x] at *
    rw [hnorm]
    dsimp [a] at hprod
    nlinarith

#print axioms inner_envelope_eq_if
end ClassifCodex

-- Complete local proof: Solutions.Classif_InnerFormulas
set_option autoImplicit false
namespace ClassifCodex

lemma logistic_inner_formula {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x₀ : Fin d → ℝ) (y₀ : ℝ) (hy₀ : y₀ = 1 ∨ y₀ = -1) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ x : Fin d → ℝ, ENNReal.ofReal (RWPI.Classif.logLoss β (x, y₀)) -
      ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x - x₀)‖) =
      if ‖WithLp.toLp p β‖ ≤ lam then ENNReal.ofReal (RWPI.Classif.logLoss β (x₀, y₀)) else ⊤ :=
  inner_envelope_eq_if p q hpq β x₀ y₀ hy₀ (fun x => RWPI.Classif.logLoss β (x, y₀))
    (fun x => logLoss_abs_sub_le p q hpq β x x₀ y₀ hy₀)
    (fun x => margin_le_logLoss β x y₀) lam hlam

lemma hinge_inner_formula {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x₀ : Fin d → ℝ) (y₀ : ℝ) (hy₀ : y₀ = 1 ∨ y₀ = -1) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ Δ : Fin d → ℝ, ENNReal.ofReal (RWPI.Classif.hingeLoss β (x₀ + Δ, y₀)) -
      ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q Δ‖) =
      if ‖WithLp.toLp p β‖ ≤ lam then ENNReal.ofReal (RWPI.Classif.hingeLoss β (x₀, y₀)) else ⊤ := by
  have he :
      (⨆ Δ : Fin d → ℝ, ENNReal.ofReal (RWPI.Classif.hingeLoss β (x₀ + Δ, y₀)) -
        ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q Δ‖) =
      ⨆ x : Fin d → ℝ, ENNReal.ofReal (RWPI.Classif.hingeLoss β (x, y₀)) -
        ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x - x₀)‖ := by
    apply le_antisymm
    · apply iSup_le
      intro Δ
      apply le_iSup_of_le (x₀ + Δ)
      rw [show x₀ + Δ - x₀ = Δ by abel]
    · apply iSup_le
      intro x
      apply le_iSup_of_le (x - x₀)
      rw [show x₀ + (x - x₀) = x by abel]
  rw [he]
  exact inner_envelope_eq_if p q hpq β x₀ y₀ hy₀ (fun x => RWPI.Classif.hingeLoss β (x, y₀))
    (fun x => hingeLoss_abs_sub_le p q hpq β x x₀ y₀ hy₀)
    (fun x => margin_le_hingeLoss β x y₀) lam hlam

#print axioms logistic_inner_formula
#print axioms hinge_inner_formula
end ClassifCodex

-- Complete local proof: Solutions.Classif_LossMeasurable
set_option autoImplicit false
namespace ClassifCodex
lemma logLoss_continuous {d : ℕ} (β : Fin d → ℝ) : Continuous (RWPI.Classif.logLoss β) := by
  have hm : Continuous (fun z : ((Fin d → ℝ) × ℝ) => -(z.2 * (β ⬝ᵥ z.1))) := by
    unfold dotProduct
    fun_prop
  have he : Continuous (fun z : ((Fin d → ℝ) × ℝ) =>
      1 + Real.exp (-(z.2 * (β ⬝ᵥ z.1)))) := continuous_const.add (Real.continuous_exp.comp hm)
  exact he.log (fun z => ne_of_gt (by positivity))
lemma hingeLoss_continuous {d : ℕ} (β : Fin d → ℝ) : Continuous (RWPI.Classif.hingeLoss β) := by
  unfold RWPI.Classif.hingeLoss dotProduct
  fun_prop
#print axioms logLoss_continuous
#print axioms hingeLoss_continuous
end ClassifCodex

-- Complete local proof: Solutions.Sol_RWPI_Classif_theorem_2
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open RWPI.Classif
theorem solution {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (hY : ∀ i, Y i = 1 ∨ Y i = -1) (p q : ℝ≥0∞) (hpq : p.HolderConjugate q)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ β : Fin d → ℝ,
      RWPI.SqrtLasso.worstCase (RWPI.SqrtLasso.Nq q) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i, Y i)))
          (logLoss β) =
        ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, logLoss β (X i, Y i) + δ * ‖WithLp.toLp p β‖)) ∧
    (∀ β : Fin d → ℝ,
      RWPI.SqrtLasso.worstCase (RWPI.SqrtLasso.Nq q) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i, Y i)))
          (hingeLoss β) =
        ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, hingeLoss β (X i, Y i) + δ * ‖WithLp.toLp p β‖)) ∧
    (⨅ β : Fin d → ℝ,
      RWPI.SqrtLasso.worstCase (RWPI.SqrtLasso.Nq q) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i, Y i)))
          (logLoss β)) =
      (⨅ β : Fin d → ℝ,
        ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, logLoss β (X i, Y i) + δ * ‖WithLp.toLp p β‖)) ∧
    (⨅ β : Fin d → ℝ,
      RWPI.SqrtLasso.worstCase (RWPI.SqrtLasso.Nq q) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i, Y i)))
          (hingeLoss β)) =
      (⨅ β : Fin d → ℝ,
        ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, hingeLoss β (X i, Y i) + δ * ‖WithLp.toLp p β‖)) := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have hlog (β : Fin d → ℝ) := ClassifCodex.risk_from_inner hn X Y q (ENNReal.HolderConjugate.one_le q p) (logLoss β)
    (ENNReal.measurable_ofReal.comp (ClassifCodex.logLoss_continuous β).measurable)
    (ClassifCodex.logLoss_nonnegative β) ‖WithLp.toLp p β‖ (norm_nonneg _)
    (fun i lam hlam => ClassifCodex.logistic_inner_formula p q hpq β (X i) (Y i) (hY i) lam hlam) δ hδ
  have hhinge (β : Fin d → ℝ) := ClassifCodex.risk_from_inner hn X Y q (ENNReal.HolderConjugate.one_le q p) (hingeLoss β)
    (ENNReal.measurable_ofReal.comp (ClassifCodex.hingeLoss_continuous β).measurable)
    (ClassifCodex.hingeLoss_nonnegative β) ‖WithLp.toLp p β‖ (norm_nonneg _)
    (fun i lam hlam => by
      exact ClassifCodex.inner_envelope_eq_if p q hpq β (X i) (Y i) (hY i)
        (fun x => hingeLoss β (x,Y i))
        (fun x => ClassifCodex.hingeLoss_abs_sub_le p q hpq β x (X i) (Y i) (hY i))
        (fun x => ClassifCodex.margin_le_hingeLoss β x (Y i)) lam hlam) δ hδ
  exact ⟨hlog, hhinge, iInf_congr hlog, iInf_congr hhinge⟩

#print axioms solution
