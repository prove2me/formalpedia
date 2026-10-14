-- Prove2me | solution 1 for ReflectedBSDE.Existence.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:49:41.576229+00:00
-- url     : https://prove2.me/submissions/e66f4352-3c90-4f41-8bb4-9ac7d6bbf9c9

import Mathlib
import Definitions.Def_ReflectedBSDE_Existence_Skorohod

open MeasureTheory Set
open scoped NNReal ENNReal


namespace ReflectedBSDE.Existence

noncomputable def skM (x : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := ⨆ s : Iic t, max (-(x s)) 0

lemma skM_bdd (x : ℝ≥0 → ℝ) (hx : Continuous x) (t : ℝ≥0) :
    BddAbove (range fun s : Iic t => max (-(x s)) 0) := by
  have hc : IsCompact (Iic t) := by rw [← Set.Icc_bot]; exact isCompact_Icc
  obtain ⟨C, hC⟩ := (hc.image (f := fun s => max (-(x s)) 0) (by fun_prop)).bddAbove
  refine ⟨C, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact hC ⟨s.1, s.2, rfl⟩

lemma le_skM {x : ℝ≥0 → ℝ} (hx : Continuous x) {s t : ℝ≥0} (h : s ≤ t) :
    max (-(x s)) 0 ≤ skM x t :=
  le_ciSup (f := fun s : Iic t => max (-(x s)) 0) (skM_bdd x hx t) ⟨s, h⟩

lemma skM_le {x : ℝ≥0 → ℝ} {t : ℝ≥0} {c : ℝ} (h : ∀ s ≤ t, max (-(x s)) 0 ≤ c) :
    skM x t ≤ c := by
  haveI : Nonempty (Iic t) := ⟨⟨t, Set.mem_Iic.2 le_rfl⟩⟩
  exact ciSup_le fun s => h s.1 s.2

lemma skM_nonneg {x : ℝ≥0 → ℝ} (hx : Continuous x) (t : ℝ≥0) : 0 ≤ skM x t :=
  (le_max_right _ _).trans (le_skM hx (le_refl t))

lemma skM_mono {x : ℝ≥0 → ℝ} (hx : Continuous x) : Monotone (skM x) :=
  fun _ _ hab => skM_le fun _ hs => le_skM hx (hs.trans hab)

lemma skM_split {x : ℝ≥0 → ℝ} (hx : Continuous x) {t1 t2 : ℝ≥0} {c : ℝ}
    (h : ∀ v, t1 < v → v ≤ t2 → max (-(x v)) 0 ≤ c) :
    skM x t2 ≤ max (skM x t1) c := skM_le fun s hs => by
  rcases le_or_gt s t1 with h1 | h1
  · exact (le_skM hx h1).trans (le_max_left _ _)
  · exact (h s h1 hs).trans (le_max_right _ _)

lemma skM_cont {x : ℝ≥0 → ℝ} (hx : Continuous x) : Continuous (skM x) := by
  rw [Metric.continuous_iff]
  intro t ε hε
  have hg : Continuous fun s => max (-(x s)) 0 := by fun_prop
  obtain ⟨δ, hδ, H⟩ := Metric.continuous_iff.1 hg t (ε/2) (by linarith)
  refine ⟨δ, hδ, fun t' ht' => ?_⟩
  rw [NNReal.dist_eq, abs_lt] at ht'
  rw [Real.dist_eq, abs_lt]
  have g_t := le_skM hx (le_refl t)
  rcases le_or_gt t t' with h | h
  · have h1 := skM_mono hx h
    have h2 : skM x t' ≤ max (skM x t) (max (-(x t)) 0 + ε/2) := skM_split hx fun v hv1 hv2 => by
      have hv1' : (t : ℝ) < v := hv1
      have hv2' : (v : ℝ) ≤ t' := hv2
      have : dist v t < δ := by
        rw [NNReal.dist_eq, abs_lt]; constructor <;> linarith
      have := H v this; rw [Real.dist_eq, abs_lt] at this; linarith
    have h3 : max (skM x t) (max (-(x t)) 0 + ε/2) ≤ skM x t + ε / 2 :=
      max_le (by linarith) (by linarith)
    constructor <;> linarith
  · have h1 := skM_mono hx h.le
    have h2 : skM x t ≤ max (skM x t') (max (-(x t)) 0 + ε/2) := skM_split hx fun v hv1 hv2 => by
      have hv1' : (t' : ℝ) < v := hv1
      have hv2' : (v : ℝ) ≤ t := hv2
      have : dist v t < δ := by
        rw [NNReal.dist_eq, abs_lt]; constructor <;> linarith
      have := H v this; rw [Real.dist_eq, abs_lt] at this; linarith
    have h4 : dist t' t < δ := by rw [NNReal.dist_eq, abs_lt]; exact ht'
    have h5 := H t' h4
    rw [Real.dist_eq, abs_lt] at h5
    have g_t' := le_skM hx (le_refl t')
    have h3 : max (skM x t') (max (-(x t)) 0 + ε/2) < skM x t' + ε :=
      max_lt (by linarith) (by linarith)
    constructor <;> linarith

lemma pathMeasure_Ioc {k : ℝ≥0 → ℝ} (hm : Monotone k) (hc : Continuous k) (a b : ℝ) :
    pathMeasure k (Ioc a b) = ENNReal.ofReal (k b.toNNReal - k a.toNNReal) := by
  unfold pathMeasure; rw [dif_pos ⟨hm, hc⟩, StieltjesFunction.measure_Ioc]; rfl

lemma lint_pos (μ : Measure ℝ) {h : ℝ → ℝ} {S : Set ℝ} (a b : ℝ) (hab : Ioc a b ⊆ S)
    {η : ℝ} (hη : 0 < η) (hh : ∀ s ∈ Ioc a b, η ≤ h s) (hμ : 0 < μ (Ioc a b)) :
    0 < ∫⁻ t in S, ENNReal.ofReal (h t) ∂μ := by
  calc (0 : ℝ≥0∞) < ENNReal.ofReal η * μ (Ioc a b) :=
        ENNReal.mul_pos (ENNReal.ofReal_pos.2 hη).ne' hμ.ne'
    _ = ∫⁻ _ in Ioc a b, ENNReal.ofReal η ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ t in Ioc a b, ENNReal.ofReal (h t) ∂μ :=
        lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioc).mono fun s hs =>
          ENNReal.ofReal_le_ofReal (hh s hs))
    _ ≤ ∫⁻ t in S, ENNReal.ofReal (h t) ∂μ := lintegral_mono_set hab

lemma sk_k_eq {x y k : ℝ≥0 → ℝ} (hx : Continuous x) (hsol : IsSkorohodSolution x y k) :
    ∀ t, k t = skM x t := by
  obtain ⟨hyk, hy0, hkc, hkm, hk0, hint⟩ := hsol
  have hyx : ∀ s, y s = x s + k s := fun s => by rw [hyk]; rfl
  intro t
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have hM0 := skM_nonneg hx t
    set A : Set ℝ≥0 := {s | k t ≤ k s} with hA
    have hAc : IsClosed A := isClosed_le continuous_const hkc
    have hAne : A.Nonempty := ⟨t, show k t ≤ k t from le_rfl⟩
    set τ := sInf A with hτdef
    have hτA : τ ∈ A := hAc.csInf_mem hAne (OrderBot.bddBelow _)
    have hτt : τ ≤ t := csInf_le (OrderBot.bddBelow _) (show t ∈ A from show k t ≤ k t from le_rfl)
    have hlow : ∀ s, s < τ → k s < k t := fun s hs => by
      by_contra hc
      push Not at hc
      have : τ ≤ s := csInf_le (OrderBot.bddBelow _) (show k t ≤ k s from hc)
      exact absurd hs (not_lt.2 this)
    have hkτ : k τ = k t := le_antisymm (hkm hτt) hτA
    have hτpos : (0 : ℝ) < τ := by
      rcases eq_or_ne τ 0 with h0 | h0
      · exfalso; rw [h0, hk0] at hkτ; linarith
      · exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)
    have hgτ := le_skM hx hτt
    have hη : 0 < y τ := by
      rw [hyx]; have := le_max_left (-(x τ)) 0; linarith
    have hyc : Continuous y := by rw [hyk]; exact hx.add hkc
    obtain ⟨δ, hδ, H⟩ := Metric.continuous_iff.1 hyc τ (y τ / 2) (by linarith)
    set a : ℝ := max ((τ : ℝ) - δ / 2) 0 with ha
    have ha0 : 0 ≤ a := le_max_right _ _
    have haτ : a < τ := max_lt (by linarith) hτpos
    have hpos := lint_pos (pathMeasure k) (h := fun s => y s.toNNReal) (S := Ici 0) a τ
      (fun s hs => le_trans ha0 hs.1.le) (half_pos hη) (fun s hs => by
        have hs0 : 0 ≤ s := ha0.trans hs.1.le
        have hd : dist s.toNNReal τ < δ := by
          rw [NNReal.dist_eq, Real.coe_toNNReal _ hs0, abs_lt]
          have : (τ : ℝ) - δ / 2 ≤ a := le_max_left _ _
          constructor <;> linarith [hs.1, hs.2]
        have := H _ hd
        rw [Real.dist_eq, abs_lt] at this
        linarith) (by
        rw [pathMeasure_Ioc hkm hkc, Real.toNNReal_coe, hkτ]
        apply ENNReal.ofReal_pos.2
        have : a.toNNReal < τ := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ha0]; exact haτ
        linarith [hlow _ this])
    rw [hint] at hpos
    exact lt_irrefl _ hpos
  · apply skM_le
    intro s hs
    apply max_le
    · have := hy0 s; rw [hyx] at this; linarith [hkm hs]
    · rw [← hk0]; exact hkm (by positivity)

lemma sk_exists {x : ℝ≥0 → ℝ} (hx : Continuous x) (hx0 : 0 ≤ x 0) :
    IsSkorohodSolution x (x + skM x) (skM x) := by
  have hc := skM_cont hx
  have hm := skM_mono hx
  refine ⟨rfl, fun t => ?_, hc, hm, ?_, ?_⟩
  · have := le_skM hx (le_refl t)
    have := le_max_left (-(x t)) 0
    show 0 ≤ x t + skM x t
    linarith
  · apply le_antisymm _ (skM_nonneg hx 0)
    apply skM_le
    intro s hs
    rw [nonpos_iff_eq_zero.1 hs]
    exact max_le (by linarith) le_rfl
  · set μ := pathMeasure (skM x)
    set U : Set ℝ := {s | 0 < (x + skM x) s.toNNReal} with hU
    have hUnull : μ U = 0 := by
      apply measure_null_of_locally_null
      intro s hs
      have hs' : 0 < x s.toNNReal + skM x s.toNNReal := hs
      set σ := s.toNNReal with hσ
      set η := x σ + skM x σ with hηdef
      have hXr : Continuous fun u : ℝ => x u.toNNReal := hx.comp continuous_real_toNNReal
      obtain ⟨δ, hδ, H⟩ := Metric.continuous_iff.1 hXr s (η / 2) (by linarith)
      refine ⟨Ioc (s - δ / 2) (s + δ / 2),
        mem_nhdsWithin_of_mem_nhds (Ioc_mem_nhds (by linarith) (by linarith)), ?_⟩
      rw [pathMeasure_Ioc hm hc]
      apply ENNReal.ofReal_eq_zero.2
      set a' := (s - δ / 2).toNNReal
      set b' := (s + δ / 2).toNNReal
      set c' := max (skM x σ - η / 2) 0
      have hbound : ∀ v : ℝ≥0, a' < v → v ≤ b' → max (-(x v)) 0 ≤ c' := by
        intro v hv1 hv2
        have h1 : s - δ / 2 ≤ (a' : ℝ) := Real.le_coe_toNNReal _
        have h1' : (a' : ℝ) < v := hv1
        have ha'0 : (0 : ℝ) ≤ a' := a'.2
        have h2 : (v : ℝ) ≤ b' := hv2
        have h2' : (b' : ℝ) = max (s + δ / 2) 0 := Real.coe_toNNReal' _
        have hvle : (v : ℝ) ≤ s + δ / 2 := by
          rw [h2'] at h2
          rcases le_max_iff.1 h2 with h | h
          · exact h
          · linarith
        have hd : dist (v : ℝ) s < δ := by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith
        have := H _ hd
        rw [Real.dist_eq, abs_lt, Real.toNNReal_coe] at this
        exact max_le_max (by linarith) le_rfl
      have hσa : a' ≤ σ := Real.toNNReal_le_toNNReal (by linarith)
      have hσb : σ ≤ b' := Real.toNNReal_le_toNNReal (by linarith)
      have e1 : skM x σ ≤ max (skM x a') c' :=
        skM_split hx fun v hv1 hv2 => hbound v hv1 (hv2.trans hσb)
      have e2 : skM x b' ≤ max (skM x σ) c' :=
        skM_split hx fun v hv1 hv2 => hbound v (lt_of_le_of_lt hσa hv1) hv2
      have hMσ := skM_nonneg hx σ
      have hMa := skM_nonneg hx a'
      have hc'le : c' ≤ skM x σ := max_le (by linarith) hMσ
      have e3 : skM x b' ≤ skM x σ := e2.trans (max_le le_rfl hc'le)
      have e4 : skM x σ ≤ skM x a' := by
        rcases le_max_iff.1 e1 with h | h
        · exact h
        · rcases le_max_iff.1 h with h' | h'
          · linarith
          · linarith
      linarith
    have hae : ∀ᵐ s ∂μ, s ∉ U := measure_eq_zero_iff_ae_notMem.1 hUnull
    rw [show (0 : ℝ≥0∞) = ∫⁻ _ in Ici (0 : ℝ), 0 ∂μ by simp]
    apply lintegral_congr_ae
    apply ae_restrict_of_ae
    filter_upwards [hae] with s hs
    exact ENNReal.ofReal_eq_zero.2 (not_lt.1 hs)

theorem lemma_2_1_core (x : ℝ≥0 → ℝ) (hx : Continuous x) (hx0 : 0 ≤ x 0) :
    (∃! p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ), IsSkorohodSolution x p.1 p.2) ∧
    ∀ y k : ℝ≥0 → ℝ, IsSkorohodSolution x y k →
      ∀ t, k t = ⨆ s : Iic t, max (-(x s)) 0 := by
  refine ⟨⟨(x + skM x, skM x), sk_exists hx hx0, fun p hp => ?_⟩,
    fun y k h t => sk_k_eq hx h t⟩
  have hk : p.2 = skM x := funext (sk_k_eq hx hp)
  have hy : p.1 = x + p.2 := hp.1
  ext1
  · rw [hy, hk]
  · exact hk

end ReflectedBSDE.Existence

open ReflectedBSDE.Existence


theorem solution (x : ℝ≥0 → ℝ) (hx : Continuous x) (hx0 : 0 ≤ x 0) :
    (∃! p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ), IsSkorohodSolution x p.1 p.2) ∧
    ∀ y k : ℝ≥0 → ℝ, IsSkorohodSolution x y k →
      ∀ t, k t = ⨆ s : Iic t, max (-(x s)) 0 := by
  exact lemma_2_1_core x hx hx0
