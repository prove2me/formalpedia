-- Prove2me | solution 1 for StochasticOrders.Convex.convex_order_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T12:21:09.505333+00:00
-- url     : https://prove2.me/submissions/95c230a7-cde1-4575-9dd9-3532e4925c2d

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder

set_option autoImplicit false

namespace StochasticOrders.Convex.CvxConv7506

open MeasureTheory ProbabilityTheory Set

/-- Lipschitz regularisation (inf-convolution with `n * |·|`). -/
noncomputable def lreg (ψ : ℝ → ℝ) (n : ℝ) (x : ℝ) : ℝ := ⨅ y, (ψ y + n * |x - y|)

lemma lreg_bdd {ψ : ℝ → ℝ} (h0 : ∀ x, 0 ≤ ψ x) {n : ℝ} (hn : 0 ≤ n) (x : ℝ) :
    BddBelow (range fun y => ψ y + n * |x - y|) :=
  ⟨0, by rintro _ ⟨y, rfl⟩; have := h0 y; positivity⟩

lemma lreg_nonneg {ψ : ℝ → ℝ} (h0 : ∀ x, 0 ≤ ψ x) {n : ℝ} (hn : 0 ≤ n) (x : ℝ) :
    0 ≤ lreg ψ n x :=
  le_ciInf fun y => by have := h0 y; positivity

lemma lreg_le_of {ψ : ℝ → ℝ} (h0 : ∀ x, 0 ≤ ψ x) {n : ℝ} (hn : 0 ≤ n) (x y : ℝ) :
    lreg ψ n x ≤ ψ y + n * |x - y| := ciInf_le (lreg_bdd h0 hn x) y

lemma lreg_le {ψ : ℝ → ℝ} (h0 : ∀ x, 0 ≤ ψ x) {n : ℝ} (hn : 0 ≤ n) (x : ℝ) :
    lreg ψ n x ≤ ψ x := by
  have := lreg_le_of h0 hn x x
  simpa using this

lemma lreg_lip {ψ : ℝ → ℝ} (h0 : ∀ x, 0 ≤ ψ x) {n : ℝ} (hn : 0 ≤ n) (x x' : ℝ) :
    lreg ψ n x ≤ lreg ψ n x' + n * |x - x'| := by
  have : lreg ψ n x - n * |x - x'| ≤ lreg ψ n x' := by
    apply le_ciInf
    intro y
    have h1 := lreg_le_of h0 hn x y
    have h2 : |x - y| ≤ |x - x'| + |x' - y| := abs_sub_le x x' y
    nlinarith [mul_le_mul_of_nonneg_left h2 hn]
  linarith

lemma lreg_mono {ψ : ℝ → ℝ} (h0 : ∀ x, 0 ≤ ψ x) {n n' : ℝ} (hn : 0 ≤ n) (hnn : n ≤ n')
    (x : ℝ) : lreg ψ n x ≤ lreg ψ n' x := by
  apply le_ciInf
  intro y
  have h1 := lreg_le_of h0 hn x y
  have h2 : n * |x - y| ≤ n' * |x - y| := mul_le_mul_of_nonneg_right hnn (abs_nonneg _)
  linarith

lemma lreg_convex {ψ : ℝ → ℝ} (h0 : ∀ x, 0 ≤ ψ x) (hψ : ConvexOn ℝ univ ψ) {n : ℝ}
    (hn : 0 ≤ n) : ConvexOn ℝ univ (lreg ψ n) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ x' _ a b ha hb hab
  simp only [smul_eq_mul]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨y, hy⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (lreg ψ n x) hε)
  obtain ⟨y', hy'⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (lreg ψ n x') hε)
  have h1 := lreg_le_of h0 hn (a * x + b * x') (a * y + b * y')
  have h2 := hψ.2 (mem_univ y) (mem_univ y') ha hb hab
  simp only [smul_eq_mul] at h2
  have h3 : |a * x + b * x' - (a * y + b * y')| ≤ a * |x - y| + b * |x' - y'| := by
    have e : a * x + b * x' - (a * y + b * y') = a * (x - y) + b * (x' - y') := by ring
    rw [e]
    calc _ ≤ |a * (x - y)| + |b * (x' - y')| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hy2 : ψ y + n * |x - y| < lreg ψ n x + ε := hy
  have hy2' : ψ y' + n * |x' - y'| < lreg ψ n x' + ε := hy'
  nlinarith [mul_le_mul_of_nonneg_left h3 hn, mul_le_mul_of_nonneg_left hy2.le ha,
    mul_le_mul_of_nonneg_left hy2'.le hb]

lemma lreg_cont {ψ : ℝ → ℝ} (h0 : ∀ x, 0 ≤ ψ x) (k : ℕ) : Continuous (lreg ψ k) := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  refine (LipschitzWith.of_dist_le_mul (K := (k : NNReal)) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_natCast, abs_sub_le_iff]
  constructor
  · linarith [lreg_lip h0 hk x y]
  · have := lreg_lip h0 hk y x
    rw [abs_sub_comm y x] at this
    linarith

lemma lreg_tendsto {ψ : ℝ → ℝ} (h0 : ∀ x, 0 ≤ ψ x) (hc : Continuous ψ) (x : ℝ) :
    Filter.Tendsto (fun k : ℕ => lreg ψ k x) Filter.atTop (nhds (ψ x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 hc x (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (ψ x / δ)
  refine ⟨N, fun k hk => ?_⟩
  have hk' : (N:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hup := lreg_le h0 hkpos x
  have hlow : ψ x - ε / 2 ≤ lreg ψ k x := by
    apply le_ciInf
    intro y
    by_cases hy : dist y x < δ
    · have h1 := hδε y hy
      rw [Real.dist_eq] at h1
      have h2 := abs_lt.1 h1
      have : 0 ≤ (k:ℝ) * |x - y| := by positivity
      linarith
    · push Not at hy
      rw [Real.dist_eq, abs_sub_comm] at hy
      have h1 : (k:ℝ) * δ ≤ k * |x - y| := mul_le_mul_of_nonneg_left hy hkpos
      have h2 : ψ x < k * δ := by
        have := (div_lt_iff₀ hδ).1 (lt_of_lt_of_le hN hk')
        linarith
      linarith [h0 y]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

lemma cont_of_convex {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) : Continuous φ :=
  continuousOn_univ.mp (hφ.continuousOn isOpen_univ)

/-- Law-level formal convex order. -/
def LawCx (P Q : Measure ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ConvexOn ℝ univ φ → Integrable φ P → Integrable φ Q →
    ∫ x, φ x ∂P ≤ ∫ x, φ x ∂Q

/-- Extended order on nonnegative convex test functions, at all shifts. -/
def RR (P Q : Measure ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, ConvexOn ℝ univ ψ → (∀ x, 0 ≤ ψ x) →
    (∃ c, ∫⁻ x, ENNReal.ofReal (ψ (x + c)) ∂P ≠ ⊤) →
    (∃ c, ∫⁻ x, ENNReal.ofReal (ψ (x + c)) ∂Q ≠ ⊤) →
    ∀ d, ∫⁻ x, ENNReal.ofReal (ψ (x + d)) ∂P ≤ ∫⁻ x, ENNReal.ofReal (ψ (x + d)) ∂Q

lemma integ_of_fin {P : Measure ℝ} {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂P ≠ ⊤) : Integrable f P := by
  have := integrable_toReal_of_lintegral_ne_top
    (hf.measurable.ennreal_ofReal.aemeasurable) hfin
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (h0 x)]

lemma pair {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : LawCx P Q) : RR P Q := by
  intro ψ hψ h0 ⟨c, hc⟩ ⟨c', hc'⟩ d
  have hcont : Continuous ψ := cont_of_convex hψ
  have hint : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (e : ℝ),
      ∫⁻ x, ENNReal.ofReal (ψ (x + e)) ∂ρ ≠ ⊤ → ∀ k : ℕ,
        Integrable (fun x => lreg ψ k (x + d)) ρ := by
    intro ρ _ e he k
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hg : Integrable (fun x => ψ (x + e) + k * |d - e|) ρ :=
      (integ_of_fin (hcont.comp (continuous_add_const e)) (fun x => h0 _) he).add
        (integrable_const _)
    refine hg.mono' ((lreg_cont h0 k).comp (continuous_add_const d)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (lreg_nonneg h0 hk _)]
    have h1 := lreg_lip h0 hk (x + d) (x + e)
    have h2 := lreg_le h0 hk (x + e)
    have e1 : x + d - (x + e) = d - e := by ring
    rw [e1] at h1
    linarith
  have hconv : ∀ k : ℕ, ConvexOn ℝ univ (fun x => lreg ψ k (x + d)) := by
    intro k
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have := (lreg_convex h0 hψ hk).2 (mem_univ (x + d)) (mem_univ (y + d)) ha hb hab
    have e : a • x + b • y + d = a • (x + d) + b • (y + d) := by
      simp only [smul_eq_mul]; linear_combination (-d) * hab
    simp only
    rw [e]
    exact this
  have hk_ineq : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (lreg ψ k (x + d)) ∂P ≤
      ∫⁻ x, ENNReal.ofReal (lreg ψ k (x + d)) ∂Q := by
    intro k
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hIP := hint P c hc k
    have hIQ := hint Q c' hc' k
    rw [← ofReal_integral_eq_lintegral_ofReal hIP
        (Filter.Eventually.of_forall fun x => lreg_nonneg h0 hk _),
      ← ofReal_integral_eq_lintegral_ofReal hIQ
        (Filter.Eventually.of_forall fun x => lreg_nonneg h0 hk _)]
    exact ENNReal.ofReal_le_ofReal (h _ (hconv k) hIP hIQ)
  have hlim : ∀ (ρ : Measure ℝ), Filter.Tendsto
      (fun k : ℕ => ∫⁻ x, ENNReal.ofReal (lreg ψ k (x + d)) ∂ρ) Filter.atTop
      (nhds (∫⁻ x, ENNReal.ofReal (ψ (x + d)) ∂ρ)) := by
    intro ρ
    refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
    · intro k
      exact (((lreg_cont h0 k).comp (continuous_add_const d)).measurable.ennreal_ofReal).aemeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      intro n n' hnn
      exact ENNReal.ofReal_le_ofReal
        (lreg_mono h0 (Nat.cast_nonneg n) (Nat.cast_le.2 hnn) _)
    · exact Filter.Eventually.of_forall fun x =>
        ENNReal.tendsto_ofReal (lreg_tendsto h0 hcont (x + d))
  exact le_of_tendsto_of_tendsto' (hlim P) (hlim Q) hk_ineq

lemma exists_fin {P : Measure ℝ} [IsProbabilityMeasure P] {f : ℝ → ENNReal}
    (h : ∫⁻ x, f x ∂P ≠ ⊤) : ∃ x, f x ≠ ⊤ := by
  by_contra hc
  push Not at hc
  apply h
  have : f = fun _ => ⊤ := funext hc
  rw [this, lintegral_const, measure_univ, mul_one]

lemma conv {P1 Q1 P2 Q2 : Measure ℝ} [IsProbabilityMeasure P1] [IsProbabilityMeasure Q1]
    [IsProbabilityMeasure P2] [IsProbabilityMeasure Q2] (h1 : RR P1 Q1) (h2 : RR P2 Q2) :
    RR ((P1.prod P2).map (fun p => p.1 + p.2)) ((Q1.prod Q2).map (fun p => p.1 + p.2)) := by
  intro ψ hψ h0 ⟨c, hc⟩ ⟨c', hc'⟩ d
  have hcont : Continuous ψ := cont_of_convex hψ
  have hm : ∀ e, Measurable (fun x => ENNReal.ofReal (ψ (x + e))) := fun e =>
    (hcont.comp (continuous_add_const e)).measurable.ennreal_ofReal
  have hm2 : ∀ e, Measurable (Function.uncurry fun x1 x2 : ℝ =>
      ENNReal.ofReal (ψ (x1 + x2 + e))) := fun e =>
    (hm e).comp (measurable_fst.add measurable_snd)
  have key : ∀ (ρ1 ρ2 : Measure ℝ) [SFinite ρ1] [SFinite ρ2] (e : ℝ),
      ∫⁻ x, ENNReal.ofReal (ψ (x + e)) ∂((ρ1.prod ρ2).map (fun p => p.1 + p.2)) =
        ∫⁻ x1, ∫⁻ x2, ENNReal.ofReal (ψ (x1 + x2 + e)) ∂ρ2 ∂ρ1 := by
    intro ρ1 ρ2 _ _ e
    rw [lintegral_map (hm e) (by fun_prop)]
    exact lintegral_prod _ ((hm e).comp (measurable_fst.add measurable_snd)).aemeasurable
  have swap : ∀ (ρ1 ρ2 : Measure ℝ) [SFinite ρ1] [SFinite ρ2] (e : ℝ),
      ∫⁻ x1, ∫⁻ x2, ENNReal.ofReal (ψ (x1 + x2 + e)) ∂ρ2 ∂ρ1 =
        ∫⁻ x2, ∫⁻ x1, ENNReal.ofReal (ψ (x1 + x2 + e)) ∂ρ1 ∂ρ2 := by
    intro ρ1 ρ2 _ _ e
    exact lintegral_lintegral_swap (hm2 e).aemeasurable
  rw [key] at hc hc' ⊢
  rw [key]
  -- finiteness facts
  have fP2 : ∃ c, ∫⁻ x, ENNReal.ofReal (ψ (x + c)) ∂P2 ≠ ⊤ := by
    obtain ⟨x1, hx1⟩ := exists_fin hc
    refine ⟨x1 + c, ?_⟩
    convert hx1 using 3 with x2
    ring_nf
  have fQ2 : ∃ c, ∫⁻ x, ENNReal.ofReal (ψ (x + c)) ∂Q2 ≠ ⊤ := by
    obtain ⟨x1, hx1⟩ := exists_fin hc'
    refine ⟨x1 + c', ?_⟩
    convert hx1 using 3 with x2
    ring_nf
  have fP1 : ∃ c, ∫⁻ x, ENNReal.ofReal (ψ (x + c)) ∂P1 ≠ ⊤ := by
    rw [swap] at hc
    obtain ⟨x2, hx2⟩ := exists_fin hc
    refine ⟨x2 + c, ?_⟩
    convert hx2 using 3 with x1
    ring_nf
  have fQ1 : ∃ c, ∫⁻ x, ENNReal.ofReal (ψ (x + c)) ∂Q1 ≠ ⊤ := by
    rw [swap] at hc'
    obtain ⟨x2, hx2⟩ := exists_fin hc'
    refine ⟨x2 + c', ?_⟩
    convert hx2 using 3 with x1
    ring_nf
  calc ∫⁻ x1, ∫⁻ x2, ENNReal.ofReal (ψ (x1 + x2 + d)) ∂P2 ∂P1
      ≤ ∫⁻ x1, ∫⁻ x2, ENNReal.ofReal (ψ (x1 + x2 + d)) ∂Q2 ∂P1 := by
        refine lintegral_mono fun x1 => ?_
        have := h2 ψ hψ h0 fP2 fQ2 (x1 + d)
        convert this using 3 with x2 x2 <;> ring_nf
    _ = ∫⁻ x2, ∫⁻ x1, ENNReal.ofReal (ψ (x1 + x2 + d)) ∂P1 ∂Q2 := swap _ _ _
    _ ≤ ∫⁻ x2, ∫⁻ x1, ENNReal.ofReal (ψ (x1 + x2 + d)) ∂Q1 ∂Q2 := by
        refine lintegral_mono fun x2 => ?_
        have := h1 ψ hψ h0 fP1 fQ1 (x2 + d)
        convert this using 3 with x1 x1 <;> ring_nf
    _ = ∫⁻ x1, ∫⁻ x2, ENNReal.ofReal (ψ (x1 + x2 + d)) ∂Q2 ∂Q1 := (swap _ _ _).symm

lemma law_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B) (h : IndepFun A B μ) :
    μ.map (fun ω => A ω + B ω) = ((μ.map A).prod (μ.map B)).map (fun p => p.1 + p.2) := by
  rw [← (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable).1 h,
    Measure.map_map (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 + p.2) (hA.prodMk hB)]
  rfl

lemma lawcx_of {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') {A : Ω → ℝ} {B : Ω' → ℝ} (hA : Measurable A)
    (hB : Measurable B) (h : ConvexOrder μ ν A B) : LawCx (μ.map A) (ν.map B) := by
  intro φ hφ hiA hiB
  have hc : Continuous φ := cont_of_convex hφ
  rw [integral_map hA.aemeasurable hc.aestronglyMeasurable,
    integral_map hB.aemeasurable hc.aestronglyMeasurable]
  exact h φ hφ ((integrable_map_measure hc.aestronglyMeasurable hA.aemeasurable).1 hiA)
    ((integrable_map_measure hc.aestronglyMeasurable hB.aemeasurable).1 hiB)

lemma sums {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, ConvexOrder μ ν (X i) (Y i)) (s : Finset (Fin m)) :
    RR (μ.map (fun ω => ∑ i ∈ s, X i ω)) (ν.map (fun ω => ∑ i ∈ s, Y i ω)) := by
  induction s using Finset.induction_on with
  | empty =>
    intro ψ _ _ _ _ d
    simp [Measure.map_const]
  | insert i s hi ih =>
    have hXs : Measurable (fun ω => ∑ j ∈ s, X j ω) := Finset.measurable_sum s (fun j _ => hX j)
    have hYs : Measurable (fun ω => ∑ j ∈ s, Y j ω) := Finset.measurable_sum s (fun j _ => hY j)
    have hIX : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) μ := by
      have := (hXindep.indepFun_finsetSum_of_notMem hX hi).symm
      convert this using 1
      funext ω
      simp [Finset.sum_apply]
    have hIY : IndepFun (Y i) (fun ω => ∑ j ∈ s, Y j ω) ν := by
      have := (hYindep.indepFun_finsetSum_of_notMem hY hi).symm
      convert this using 1
      funext ω
      simp [Finset.sum_apply]
    simp only [Finset.sum_insert hi]
    rw [law_sum μ (hX i) hXs hIX, law_sum ν (hY i) hYs hIY]
    have : IsProbabilityMeasure (μ.map (X i)) := Measure.isProbabilityMeasure_map (hX i).aemeasurable
    have : IsProbabilityMeasure (ν.map (Y i)) := Measure.isProbabilityMeasure_map (hY i).aemeasurable
    have : IsProbabilityMeasure (μ.map (fun ω => ∑ j ∈ s, X j ω)) :=
      Measure.isProbabilityMeasure_map hXs.aemeasurable
    have : IsProbabilityMeasure (ν.map (fun ω => ∑ j ∈ s, Y j ω)) :=
      Measure.isProbabilityMeasure_map hYs.aemeasurable
    exact conv (pair (lawcx_of μ ν (hX i) (hY i) (hord i))) ih

lemma trunc_lim {φ : ℝ → ℝ} (hc : Continuous φ) {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) [IsProbabilityMeasure ρ]
    (Z : α → ℝ) (hZ : Measurable Z) (hiZ : Integrable (φ ∘ Z) ρ) :
    Filter.Tendsto (fun n : ℕ => ∫ ω, max (φ (Z ω)) (-(n:ℝ)) ∂ρ) Filter.atTop
      (nhds (∫ ω, φ (Z ω) ∂ρ)) := by
  refine tendsto_integral_of_dominated_convergence (fun ω => |φ (Z ω)|) ?_ hiZ.abs ?_ ?_
  · intro n
    exact ((hc.measurable.comp hZ).max measurable_const).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_le]
    have h1 := neg_abs_le (φ (Z ω))
    have h2 := le_abs_self (φ (Z ω))
    have h3 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    constructor
    · exact le_trans h1 (le_max_left _ _)
    · exact max_le h2 (by linarith [abs_nonneg (φ (Z ω))])
  · refine Filter.Eventually.of_forall fun ω => ?_
    apply tendsto_const_nhds.congr'
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨⌈-φ (Z ω)⌉₊, fun n hn => ?_⟩
    have : -φ (Z ω) ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    exact (max_eq_left (by linarith)).symm

lemma final {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Ω → ℝ} {T : Ω' → ℝ} (hS : Measurable S) (hT : Measurable T)
    (hR : RR (μ.map S) (ν.map T)) : ConvexOrder μ ν S T := by
  intro φ hφ hiS hiT
  have hc : Continuous φ := cont_of_convex hφ
  have step : ∀ n : ℕ, ∫ ω, max (φ (S ω)) (-(n:ℝ)) ∂μ ≤ ∫ ω, max (φ (T ω)) (-(n:ℝ)) ∂ν := by
    intro n
    set ψ : ℝ → ℝ := fun x => max (φ x + n) 0 with hψdef
    have hψc : ConvexOn ℝ univ ψ :=
      (hφ.add (convexOn_const (n:ℝ) convex_univ)).sup (convexOn_const 0 convex_univ)
    have hψ0 : ∀ x, 0 ≤ ψ x := fun x => le_max_right _ _
    have hψcont : Continuous ψ := (hc.add continuous_const).max continuous_const
    have hψS : Integrable (fun ω => ψ (S ω)) μ := (hiS.add (integrable_const (n:ℝ))).pos_part
    have hψT : Integrable (fun ω => ψ (T ω)) ν := (hiT.add (integrable_const (n:ℝ))).pos_part
    have hmψ : Measurable (fun x => ENNReal.ofReal (ψ (x + 0))) :=
      (hψcont.comp (continuous_add_const 0)).measurable.ennreal_ofReal
    have eS : ∫⁻ x, ENNReal.ofReal (ψ (x + 0)) ∂(μ.map S) = ENNReal.ofReal (∫ ω, ψ (S ω) ∂μ) := by
      rw [lintegral_map hmψ hS, ofReal_integral_eq_lintegral_ofReal hψS
        (Filter.Eventually.of_forall fun x => hψ0 _)]
      simp
    have eT : ∫⁻ x, ENNReal.ofReal (ψ (x + 0)) ∂(ν.map T) = ENNReal.ofReal (∫ ω, ψ (T ω) ∂ν) := by
      rw [lintegral_map hmψ hT, ofReal_integral_eq_lintegral_ofReal hψT
        (Filter.Eventually.of_forall fun x => hψ0 _)]
      simp
    have hle := hR ψ hψc hψ0 ⟨0, by rw [eS]; exact ENNReal.ofReal_ne_top⟩
      ⟨0, by rw [eT]; exact ENNReal.ofReal_ne_top⟩ 0
    rw [eS, eT] at hle
    have hle' := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun ω => hψ0 _)).1 hle
    have e : ∀ x, max (φ x) (-(n:ℝ)) = ψ x - n := by
      intro x
      simp only [hψdef]
      rcases le_total (φ x) (-(n:ℝ)) with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
    simp only [e]
    rw [integral_sub hψS (integrable_const _), integral_sub hψT (integrable_const _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith
  exact le_of_tendsto_of_tendsto' (trunc_lim hc μ S hS hiS) (trunc_lim hc ν T hT hiT) step

end StochasticOrders.Convex.CvxConv7506

open MeasureTheory ProbabilityTheory StochasticOrders.Convex in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, ConvexOrder μ ν (X i) (Y i)) :
    ConvexOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω) := by
  have hS := StochasticOrders.Convex.CvxConv7506.sums μ ν X Y hX hY hXindep hYindep hord
    Finset.univ
  exact StochasticOrders.Convex.CvxConv7506.final μ ν
    (Finset.measurable_sum _ fun i _ => hX i) (Finset.measurable_sum _ fun i _ => hY i) hS
