-- Prove2me | solution 1 for StochKolmogorov.Classify.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T08:43:43.290794+00:00
-- url     : https://prove2.me/submissions/ba6a358e-b5ec-4d50-a662-c02e74859199

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

set_option autoImplicit false
set_option linter.all false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace L56

section Abstract

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- Clipping `v` to `[-M, M]`. -/
noncomputable def clip (M v : ℝ) : ℝ := max (-M) (min M v)

lemma clip_abs_le (M v : ℝ) (hM : 0 ≤ M) : |clip M v| ≤ M := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clip_tail (M v : ℝ) (hM : 0 ≤ M) :
    |v - clip M v| ≤ |v| ∧ (|v| ≤ M → v - clip M v = 0) := by
  unfold clip
  rcases le_total v M with h1 | h1 <;> rcases le_total (-M) v with h2 | h2
  · rw [min_eq_right h1, max_eq_right h2]; simp
  · rw [min_eq_right h1, max_eq_left h2]
    constructor
    · rw [abs_of_nonpos (by linarith : v ≤ 0), abs_le]; constructor <;> linarith
    · intro h
      rw [abs_le] at h
      have : v = -M := by linarith
      rw [this]; ring
  · rw [min_eq_left h1, max_eq_right (by linarith : -M ≤ M)]
    constructor
    · rw [abs_of_nonneg (by linarith : 0 ≤ v), abs_le]; constructor <;> linarith
    · intro h
      rw [abs_le] at h
      have : v = M := by linarith
      rw [this]; ring
  · obtain ⟨hM0, hv0⟩ : M = 0 ∧ v = 0 := ⟨by linarith, by linarith⟩
    subst hM0; subst hv0; simp

lemma bcf_tendsto (μ : ℕ → Measure E) (π : Measure E)
    (hw : ∀ f : E →ᵇ ℝ, Tendsto (fun k => ∫ y, f y ∂(μ k)) atTop (𝓝 (∫ y, f y ∂π)))
    (f : E → ℝ) (hf : Continuous f) (C : ℝ) (hC : ∀ y, |f y| ≤ C) :
    Tendsto (fun k => ∫ y, f y ∂(μ k)) atTop (𝓝 (∫ y, f y ∂π)) :=
  hw (BoundedContinuousFunction.ofNormedAddCommGroup f hf C
    (fun y => (Real.norm_eq_abs (f y)).le.trans (hC y)))

lemma integrable_of_lintegral (ν : Measure E) (G : E → ℝ) (hG : Continuous G)
    (hG0 : ∀ y, 0 ≤ G y) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∫⁻ y, ENNReal.ofReal (G y) ∂ν ≤ ENNReal.ofReal K) :
    Integrable G ν ∧ ∫ y, G y ∂ν ≤ K := by
  have hint : Integrable G ν := by
    refine ⟨hG.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)]
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0)
    hG.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hK hb

/-- Uniform integrability along a weakly convergent sequence: if the weight `G` has
uniformly bounded integrals and `H` is eventually dominated by `η G` for every `η > 0`,
then `∫ H dμ_k → ∫ H dπ`. -/
theorem ui_conv (μ : ℕ → Measure E) (π : Measure E) [IsFiniteMeasure π]
    (G H : E → ℝ) (hG : Continuous G) (hG0 : ∀ y, 0 ≤ G y) (hH : Continuous H)
    (K : ℝ) (hK : 0 ≤ K)
    (hbd : ∀ᶠ k in atTop, IsFiniteMeasure (μ k) ∧
      ∫⁻ y, ENNReal.ofReal (G y) ∂(μ k) ≤ ENNReal.ofReal K)
    (hw : ∀ f : E →ᵇ ℝ, Tendsto (fun k => ∫ y, f y ∂(μ k)) atTop (𝓝 (∫ y, f y ∂π)))
    (htail : ∀ η > 0, ∃ M : ℝ, ∀ y, M < |H y| → |H y| ≤ η * G y) :
    Integrable H π ∧ Tendsto (fun k => ∫ y, H y ∂(μ k)) atTop (𝓝 (∫ y, H y ∂π)) := by
  -- step 1: the weight has integral `≤ K` under `π`
  have hbdk : ∀ᶠ k in atTop, IsFiniteMeasure (μ k) ∧ Integrable G (μ k) ∧
      ∫ y, G y ∂(μ k) ≤ K := by
    filter_upwards [hbd] with k hk
    exact ⟨hk.1, integrable_of_lintegral (μ k) G hG hG0 K hK hk.2⟩
  have hminN : ∀ N : ℕ, ∫ y, min (G y) (N : ℝ) ∂π ≤ K := by
    intro N
    have hc : Continuous fun y => min (G y) (N : ℝ) := hG.min continuous_const
    have hb : ∀ y, |min (G y) (N : ℝ)| ≤ N := by
      intro y
      rw [abs_of_nonneg (le_min (hG0 y) (Nat.cast_nonneg N))]
      exact min_le_right _ _
    refine le_of_tendsto (bcf_tendsto μ π hw _ hc N hb) ?_
    filter_upwards [hbdk] with k hk
    haveI := hk.1
    calc ∫ y, min (G y) (N : ℝ) ∂(μ k) ≤ ∫ y, G y ∂(μ k) := by
          refine integral_mono (Integrable.of_bound hc.aestronglyMeasurable N
            (Filter.Eventually.of_forall fun y => (Real.norm_eq_abs _).le.trans (hb y)))
            hk.2.1 (fun y => min_le_left _ _)
      _ ≤ K := hk.2.2
  have hlinπ : ∫⁻ y, ENNReal.ofReal (G y) ∂π ≤ ENNReal.ofReal K := by
    have hsup : ∀ y, ENNReal.ofReal (G y) = ⨆ N : ℕ, ENNReal.ofReal (min (G y) (N : ℝ)) := by
      intro y
      apply le_antisymm
      · refine le_iSup_of_le ⌈G y⌉₊ ?_
        rw [min_eq_left (Nat.le_ceil _)]
      · exact iSup_le fun N => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    simp_rw [hsup]
    rw [lintegral_iSup]
    · refine iSup_le fun N => ?_
      have hc : Continuous fun y => min (G y) (N : ℝ) := hG.min continuous_const
      rw [← ofReal_integral_eq_lintegral_ofReal
        (Integrable.of_bound hc.aestronglyMeasurable N
          (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hG0 y) (Nat.cast_nonneg N))]
            exact min_le_right _ _))
        (Filter.Eventually.of_forall fun y => le_min (hG0 y) (Nat.cast_nonneg N))]
      exact ENNReal.ofReal_le_ofReal (hminN N)
    · intro N
      exact (hG.min continuous_const).measurable.ennreal_ofReal
    · intro N₁ N₂ hN y
      exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.2 hN))
  obtain ⟨hGπ, hGπK⟩ := integrable_of_lintegral π G hG hG0 K hK hlinπ
  -- step 2: integrability of `H`
  obtain ⟨M1, hM1⟩ := htail 1 one_pos
  have hHint : ∀ ν : Measure E, IsFiniteMeasure ν → Integrable G ν → Integrable H ν := by
    intro ν hν hGν
    refine Integrable.mono' ((integrable_const (max M1 0)).add hGν) hH.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    by_cases hy : M1 < |H y|
    · have := hM1 y hy
      have := hG0 y
      have := le_max_right M1 0
      show |H y| ≤ max M1 0 + G y
      linarith
    · push Not at hy
      have := hG0 y
      have := le_max_left M1 0
      show |H y| ≤ max M1 0 + G y
      linarith
  refine ⟨hHint π inferInstance hGπ, ?_⟩
  -- step 3: convergence
  rw [Metric.tendsto_nhds]
  intro η hη
  set ε' : ℝ := η / (4 * (K + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  have hε'K : ε' * K ≤ η / 4 := by
    rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨M0, hM0⟩ := htail ε' hε'pos
  set M : ℝ := max M0 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hclipc : Continuous fun y => clip M (H y) :=
    continuous_const.max (continuous_const.min hH)
  have hclipb : ∀ y, |clip M (H y)| ≤ M := fun y => clip_abs_le M (H y) hM
  have htailpt : ∀ y, |H y - clip M (H y)| ≤ ε' * G y := by
    intro y
    obtain ⟨t1, t2⟩ := clip_tail M (H y) hM
    by_cases hy : |H y| ≤ M
    · rw [t2 hy, abs_zero]; exact mul_nonneg hε'pos.le (hG0 y)
    · push Not at hy
      exact t1.trans (hM0 y (lt_of_le_of_lt (le_max_left _ _) hy))
  have key : ∀ ν : Measure E, IsFiniteMeasure ν → Integrable G ν → ∫ y, G y ∂ν ≤ K →
      |∫ y, H y ∂ν - ∫ y, clip M (H y) ∂ν| ≤ ε' * K := by
    intro ν hν hGν hGK
    have hci : Integrable (fun y => clip M (H y)) ν :=
      Integrable.of_bound hclipc.aestronglyMeasurable M
        (Filter.Eventually.of_forall fun y => (Real.norm_eq_abs _).le.trans (hclipb y))
    rw [← integral_sub (hHint ν hν hGν) hci]
    calc |∫ y, (H y - clip M (H y)) ∂ν| ≤ ∫ y, |H y - clip M (H y)| ∂ν :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, ε' * G y ∂ν :=
          integral_mono ((hHint ν hν hGν).sub hci).abs (hGν.const_mul ε') htailpt
      _ = ε' * ∫ y, G y ∂ν := integral_const_mul _ _
      _ ≤ ε' * K := mul_le_mul_of_nonneg_left hGK hε'pos.le
  have hπkey := key π inferInstance hGπ hGπK
  have hconv := (Metric.tendsto_nhds.1
    (bcf_tendsto μ π hw _ hclipc M hclipb)) (η / 2) (by positivity)
  filter_upwards [hconv, hbdk] with k hk1 hk2
  have hkkey := key (μ k) hk2.1 hk2.2.1 hk2.2.2
  rw [Real.dist_eq] at hk1 ⊢
  have e1 := abs_sub_le (∫ y, H y ∂(μ k)) (∫ y, clip M (H y) ∂(μ k)) (∫ y, H y ∂π)
  have e2 := abs_sub_le (∫ y, clip M (H y) ∂(μ k)) (∫ y, clip M (H y) ∂π) (∫ y, H y ∂π)
  rw [abs_sub_comm (∫ y, clip M (H y) ∂π)] at e2
  linarith

end Abstract

end L56

namespace L56K

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

lemma continuous_posPart : Continuous (StochKolmogorov.Classify.posPart (n := n)) := by
  unfold StochKolmogorov.Classify.posPart
  first
  | fun_prop
  | exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).max
        continuous_const)

lemma posPart_mem (y : SDEState n) : StochKolmogorov.Classify.posPart y ∈ orthant n := by
  intro i; simp [StochKolmogorov.Classify.posPart]

lemma posPart_eq_of_mem {y : SDEState n} (hy : y ∈ orthant n) : StochKolmogorov.Classify.posPart y = y := by
  ext i; simp [StochKolmogorov.Classify.posPart, max_eq_left (hy i)]

lemma cont_comp_posPart {φ : SDEState n → ℝ} (h : ContinuousOn φ (orthant n)) :
    Continuous fun y => φ (StochKolmogorov.Classify.posPart y) :=
  h.comp_continuous continuous_posPart posPart_mem

theorem measurableSet_orthant : MeasurableSet (orthant n) := by
  have e : orthant n = ⋂ i, {x : SDEState n | 0 ≤ x i} := by
    ext x; simp [orthant]
  rw [e]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le measurable_const (PiLp.continuous_apply 2 _ i).measurable

lemma continuous_weight (C : Coeffs n) (c : SDEState n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hfc : ∀ i, ContinuousOn (C.f i) (orthant n)) (hgc : ∀ i, ContinuousOn (C.g i) (orthant n)) :
    Continuous fun y => growthWeight C c δ (StochKolmogorov.Classify.posPart y) := by
  have hco : ∀ i, Continuous fun y : SDEState n => (StochKolmogorov.Classify.posPart y) i := fun i =>
    (PiLp.continuous_apply 2 _ i).comp continuous_posPart
  have hf : ∀ i, Continuous fun y => C.f i (StochKolmogorov.Classify.posPart y) := fun i => cont_comp_posPart (hfc i)
  have hg : ∀ i, Continuous fun y => C.g i (StochKolmogorov.Classify.posPart y) := fun i => cont_comp_posPart (hgc i)
  simp only [growthWeight]
  exact Continuous.mul
    (Continuous.rpow_const (continuous_const.add
      (continuous_finset_sum _ fun i _ => continuous_const.mul (hco i))) (fun _ => Or.inr hδ))
    (continuous_const.add (continuous_finset_sum _ fun i _ => ((hf i).abs).add ((hg i).pow 2)))

lemma weight_nonneg (C : Coeffs n) {c : SDEState n} (hc : c ∈ openOrthant n) (δ : ℝ)
    {y : SDEState n} (hy : y ∈ orthant n) : 0 ≤ growthWeight C c δ y := by
  unfold growthWeight
  have h1 : 0 ≤ ∑ i, c i * y i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hy i)
  have h2 : 0 ≤ ∑ i, (|C.f i y| + C.g i y ^ 2) :=
    Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (sq_nonneg _)
  exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith)

/-- `occ` is a finite measure, carried by the orthant, with the expected weight bound. -/
lemma occ_facts {Ω : Type*} (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hpath : ∀ t, X x t ω ∈ orthant n) (W : SDEState n → ℝ) (hW : Continuous W)
    (t A : ℝ) (ht : 0 < t) (hA : 0 ≤ A)
    (hb : ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (W (X x s.toNNReal ω))
      ≤ ENNReal.ofReal (A * t)) :
    IsFiniteMeasure (occ X x t ω) ∧ occ X x t ω (orthant n)ᶜ = 0 ∧
      ∫⁻ y, ENNReal.ofReal (W y) ∂(occ X x t ω) ≤ ENNReal.ofReal A := by
  have h0 : ENNReal.ofReal t ≠ 0 := by simpa using ht
  have htop : ENNReal.ofReal t ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · unfold occ
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 h0)) (measure_lt_top _ _)
  · unfold occ
    rw [Measure.smul_apply, smul_eq_mul]
    by_cases hm : AEMeasurable (fun s : ℝ => X x s.toNNReal ω) (volume.restrict (Set.Icc (0 : ℝ) t))
    · rw [Measure.map_apply_of_aemeasurable hm measurableSet_orthant.compl]
      have : (fun s : ℝ => X x s.toNNReal ω) ⁻¹' (orthant n)ᶜ = ∅ := by
        ext s; simp [hpath s.toNNReal]
      rw [this, measure_empty, mul_zero]
    · rw [Measure.map_of_not_aemeasurable hm]; simp
  · unfold occ
    rw [lintegral_smul_measure]
    by_cases hm : AEMeasurable (fun s : ℝ => X x s.toNNReal ω) (volume.restrict (Set.Icc (0 : ℝ) t))
    · rw [lintegral_map' hW.measurable.ennreal_ofReal.aemeasurable hm]
      calc (ENNReal.ofReal t)⁻¹ * ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (W (X x s.toNNReal ω))
          ≤ (ENNReal.ofReal t)⁻¹ * (ENNReal.ofReal A * ENNReal.ofReal t) := by
            rw [← ENNReal.ofReal_mul hA]; exact mul_le_mul' le_rfl hb
        _ = ENNReal.ofReal A := by
            rw [mul_comm (ENNReal.ofReal A), ← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
    · rw [Measure.map_of_not_aemeasurable hm]; simp

end L56K

open MeasureTheory ProbabilityTheory Filter ENNReal NNReal Topology BoundedContinuousFunction StochKolmogorov.Classify EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (δ₁ : ℝ) (h14 : Assumption14 C δ₁) (hδ₁ : δ₁ ≤ δ₀) :
    ∀ x ∈ orthant n, ∀ ω : Ω, (∀ t, X x t ω ∈ orthant n) → ∀ Khat : ℝ,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t)) →
      ∀ (Ts : ℕ → ℝ) (π : Measure (SDEState n)), Tendsto Ts atTop atTop → IsInvariant P X π →
      (∀ h : SDEState n →ᵇ ℝ,
        Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π))) →
      ∀ (h : SDEState n → ℝ) (Kh δ : ℝ), ContinuousOn h (orthant n) → 0 < Kh → 0 ≤ δ →
        δ < δ₁ → (∀ y ∈ orthant n, |h y| < Kh * growthWeight C c δ y) →
        Integrable h π ∧
          Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π)) := by
  intro x hx ω hpath Khat hK Ts π hTs hπ hw h Kh δ hh hKh hδ hδδ₁ hhb
  haveI : IsProbabilityMeasure π := hπ.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hfc : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hA.2.1 i).1.continuousOn
  have hgc : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hA.2.1 i).2.continuousOn
  set G : SDEState n → ℝ := fun y => growthWeight C c δ₁ (StochKolmogorov.Classify.posPart y) with hGdef
  set H : SDEState n → ℝ := fun y => h (StochKolmogorov.Classify.posPart y) with hHdef
  have hGc : Continuous G := L56K.continuous_weight C c δ₁ h14.1.le hfc hgc
  have hG0 : ∀ y, 0 ≤ G y := fun y => L56K.weight_nonneg C hc δ₁ (L56K.posPart_mem y)
  have hHc : Continuous H := L56K.cont_comp_posPart hh
  set A : ℝ := max (Khat + 1) 0 with hAdef
  have hA0 : 0 ≤ A := le_max_right _ _
  -- eventual facts about the occupation measures
  have hev : ∀ᶠ k in atTop, IsFiniteMeasure (occ X x (Ts k) ω) ∧
      occ X x (Ts k) ω (orthant n)ᶜ = 0 ∧
      ∫⁻ y, ENNReal.ofReal (G y) ∂(occ X x (Ts k) ω) ≤ ENNReal.ofReal A := by
    have h1 := hTs.eventually (hK 1 one_pos)
    have h2 := hTs.eventually (eventually_gt_atTop 0)
    filter_upwards [h1, h2] with k hk1 hk2
    refine L56K.occ_facts X x ω hpath G hGc (Ts k) A hk2 hA0 ?_
    have e : ∀ s : ℝ, G (X x s.toNNReal ω) = growthWeight C c δ₁ (X x s.toNNReal ω) := by
      intro s; simp only [hGdef, L56K.posPart_eq_of_mem (hpath _)]
    simp_rw [e]
    refine hk1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hk2.le
  -- tail domination
  have htail : ∀ η > 0, ∃ M : ℝ, ∀ y, M < |H y| → |H y| ≤ η * G y := by
    intro η hη
    have hlim := tendsto_rpow_neg_atTop (show 0 < δ₁ - δ by linarith)
    obtain ⟨r, hr⟩ := ((hlim.eventually (gt_mem_nhds (show (0 : ℝ) < η / Kh by positivity))).and
      (eventually_ge_atTop 1)).exists
    have hr1 : 1 ≤ r := hr.2
    have hr2 : r ^ (-(δ₁ - δ)) < η / Kh := hr.1
    have hcpos : ∀ i, 0 < c i := hc
    set Bx : Set (SDEState n) :=
      (WithLp.toLp 2) '' (Set.univ.pi fun i => Set.Icc (0 : ℝ) (r / c i)) with hBx
    have hBc : IsCompact Bx :=
      (isCompact_univ_pi fun i => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
    obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hHc.continuousOn
    refine ⟨M, fun y hy => ?_⟩
    set z := StochKolmogorov.Classify.posPart y with hz
    have hzmem : z ∈ orthant n := L56K.posPart_mem y
    have hHz : H z = H y := by
      simp only [hHdef, hz]
      rw [L56K.posPart_eq_of_mem (L56K.posPart_mem y)]
    have hnot : ∃ i, r / c i < z i := by
      by_contra hcon
      push Not at hcon
      have hzB : z ∈ Bx := ⟨WithLp.ofLp z, fun i _ => ⟨hzmem i, hcon i⟩, by simp⟩
      have := hM z hzB
      rw [Real.norm_eq_abs, hHz] at this
      linarith
    obtain ⟨i, hi⟩ := hnot
    have hS0 : 0 ≤ ∑ j, c j * z j := Finset.sum_nonneg fun j _ => mul_nonneg (hcpos j).le (hzmem j)
    have hci : r < c i * z i := by
      rw [div_lt_iff₀ (hcpos i)] at hi; linarith
    have hsingle : c i * z i ≤ ∑ j, c j * z j :=
      Finset.single_le_sum (f := fun j => c j * z j)
        (fun j _ => mul_nonneg (hcpos j).le (hzmem j)) (Finset.mem_univ i)
    set u : ℝ := 1 + ∑ j, c j * z j with hu
    have hur : r ≤ u := by linarith
    have hupos : 0 < u := by linarith
    have hR : 0 ≤ 1 + ∑ j, (|C.f j z| + C.g j z ^ 2) := by
      have := Finset.sum_nonneg (s := Finset.univ)
        (fun j (_ : j ∈ Finset.univ) => add_nonneg (abs_nonneg (C.f j z)) (sq_nonneg (C.g j z)))
      linarith
    have hpow : u ^ δ ≤ u ^ δ₁ * r ^ (-(δ₁ - δ)) := by
      have e : u ^ δ = u ^ δ₁ * u ^ (-(δ₁ - δ)) := by
        rw [← Real.rpow_add hupos]; ring_nf
      rw [e]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith) hur (by linarith))
        (Real.rpow_nonneg hupos.le _)
    have hbz := hhb z hzmem
    have hGz : G y = u ^ δ₁ * (1 + ∑ j, (|C.f j z| + C.g j z ^ 2)) := rfl
    have hHy : H y = h z := rfl
    rw [hHy, hGz]
    have hwδ : growthWeight C c δ z = u ^ δ * (1 + ∑ j, (|C.f j z| + C.g j z ^ 2)) := rfl
    rw [hwδ] at hbz
    have hrK : Kh * r ^ (-(δ₁ - δ)) ≤ η := by
      have := hr2.le
      rw [le_div_iff₀ hKh] at this; linarith
    have hu1 : 0 ≤ u ^ δ₁ := Real.rpow_nonneg hupos.le _
    have hr0 : 0 ≤ r ^ (-(δ₁ - δ)) := Real.rpow_nonneg (by linarith) _
    calc |h z| ≤ Kh * (u ^ δ * (1 + ∑ j, (|C.f j z| + C.g j z ^ 2))) := hbz.le
      _ ≤ Kh * ((u ^ δ₁ * r ^ (-(δ₁ - δ))) * (1 + ∑ j, (|C.f j z| + C.g j z ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hR) hKh.le
      _ = (Kh * r ^ (-(δ₁ - δ))) * (u ^ δ₁ * (1 + ∑ j, (|C.f j z| + C.g j z ^ 2))) := by ring
      _ ≤ η * (u ^ δ₁ * (1 + ∑ j, (|C.f j z| + C.g j z ^ 2))) :=
          mul_le_mul_of_nonneg_right hrK (mul_nonneg hu1 hR)
  obtain ⟨hHπ, hconv⟩ := L56.ui_conv (fun k => occ X x (Ts k) ω) π G H hGc hG0 hHc A hA0
    (hev.mono fun k hk => ⟨hk.1, hk.2.2⟩) hw htail
  have haeπ : ∀ᵐ y ∂π, H y = h y := by
    have : ∀ᵐ y ∂π, y ∈ orthant n := ae_iff.2 hπ.2.1
    filter_upwards [this] with y hy
    simp only [hHdef, L56K.posPart_eq_of_mem hy]
  refine ⟨hHπ.congr haeπ, ?_⟩
  rw [← integral_congr_ae haeπ]
  refine hconv.congr' ?_
  filter_upwards [hev] with k hk
  have : ∀ᵐ y ∂(occ X x (Ts k) ω), H y = h y := by
    have h2 : ∀ᵐ y ∂(occ X x (Ts k) ω), y ∈ orthant n := ae_iff.2 hk.2.1
    filter_upwards [h2] with y hy
    simp only [hHdef, L56K.posPart_eq_of_mem hy]
  exact integral_congr_ae this
