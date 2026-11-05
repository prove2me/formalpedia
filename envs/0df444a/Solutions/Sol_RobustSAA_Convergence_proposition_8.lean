-- Prove2me | solution 1 for RobustSAA.Convergence.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:15:51.579903+00:00
-- url     : https://prove2.me/submissions/0d4e5f24-85f1-4b18-999c-5796cbf25f96

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped NNReal ENNReal
open RobustSAA.Convergence

namespace RSAAProp8Aux

variable {d : ℕ} {Ξ : Set (Pt d)}

lemma integrable_of_lintegral {μ : Measure ↥Ξ} {φ : ↥Ξ → ℝ≥0} (hφc : Continuous φ)
    (h : ∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂μ < ⊤) : Integrable (fun ξ => (φ ξ : ℝ)) μ := by
  have := integrable_toReal_of_lintegral_ne_top
    (μ := μ) (f := fun ξ => (φ ξ : ℝ≥0∞)) (by fun_prop) h.ne
  simpa using this

lemma integral_eq_lintegral {μ : Measure ↥Ξ} {φ : ↥Ξ → ℝ≥0} (hφc : Continuous φ) :
    ∫ ξ, (φ ξ : ℝ) ∂μ = (∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂μ).toReal := by
  have := integral_toReal (μ := μ) (f := fun ξ => (φ ξ : ℝ≥0∞)) (by fun_prop)
    (Eventually.of_forall fun ξ => ENNReal.coe_lt_top)
  simpa using this

/-- Truncation from above of `ψ = φ` at level `n`, as a bounded continuous function. -/
noncomputable def trunc (φ : ↥Ξ → ℝ≥0) (hφc : Continuous φ) (n : ℕ) : ↥Ξ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun ξ => min (φ ξ : ℝ) n)
    ((NNReal.continuous_coe.comp hφc).min continuous_const) n (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (NNReal.coe_nonneg _) (Nat.cast_nonneg n))]
      exact min_le_right _ _)

/-- Clamping of `f` to `[-L, L]`, as a bounded continuous function. -/
noncomputable def clamp (f : ↥Ξ → ℝ) (hf : Continuous f) (L : ℝ) (hL : 0 ≤ L) : ↥Ξ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun ξ => max (min (f ξ) L) (-L))
    ((hf.min continuous_const).max continuous_const) L (fun ξ => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · exact le_max_right _ _
      · exact max_le (min_le_right _ _) (by linarith))

lemma clamp_close (f : ↥Ξ → ℝ) (hf : Continuous f) {ν η : ℝ} (hν : 0 ≤ ν) (hη : 0 ≤ η)
    (φ : ↥Ξ → ℝ≥0) (hb : ∀ ξ, |f ξ| ≤ ν + η * φ ξ) (n : ℕ) (ξ : ↥Ξ) :
    |f ξ - clamp f hf (ν + η * n) (by positivity) ξ| ≤
      η * ((φ ξ : ℝ) - min (φ ξ : ℝ) n) := by
  have hL : 0 ≤ ν + η * n := by positivity
  show |f ξ - max (min (f ξ) (ν + η * n)) (-(ν + η * n))| ≤ η * ((φ ξ : ℝ) - min (φ ξ : ℝ) n)
  have hbξ := hb ξ
  rw [abs_le] at hbξ
  have hτ : 0 ≤ (φ ξ : ℝ) - min (φ ξ : ℝ) n := by linarith [min_le_left (φ ξ : ℝ) n]
  have hτ2 : (φ ξ : ℝ) - n ≤ (φ ξ : ℝ) - min (φ ξ : ℝ) n := by linarith [min_le_right (φ ξ : ℝ) n]
  have h0 : 0 ≤ η * ((φ ξ : ℝ) - min (φ ξ : ℝ) n) := mul_nonneg hη hτ
  have h1 : η * ((φ ξ : ℝ) - n) ≤ η * ((φ ξ : ℝ) - min (φ ξ : ℝ) n) :=
    mul_le_mul_of_nonneg_left hτ2 hη
  rcases le_or_gt (f ξ) (ν + η * n) with h | h
  · rw [min_eq_left h]
    rcases le_or_gt (-(ν + η * n)) (f ξ) with h' | h'
    · rw [max_eq_left h', sub_self, abs_zero]; exact h0
    · rw [max_eq_right h'.le, abs_le]
      constructor <;> nlinarith
  · rw [min_eq_right h.le, max_eq_left (by linarith), abs_le]
    constructor <;> nlinarith

/-- Weak convergence plus convergence of the `φ`-moment gives convergence of expectations of any
continuous `f = O(φ)` (uniform integrability via truncation). -/
lemma ui_conv {G : ℕ → ProbabilityMeasure ↥Ξ} {F : ProbabilityMeasure ↥Ξ}
    (hGF : Tendsto G atTop (𝓝 F)) {φ : ↥Ξ → ℝ≥0} (hφc : Continuous φ)
    (hφF : ∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(F : Measure ↥Ξ) < ⊤)
    (hφconv : Tendsto (fun N => ∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(G N : Measure ↥Ξ)) atTop
      (𝓝 (∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(F : Measure ↥Ξ))))
    {f : ↥Ξ → ℝ} (hf : Continuous f) {ν η : ℝ} (hν : 0 ≤ ν) (hη : 0 ≤ η)
    (hb : ∀ ξ, |f ξ| ≤ ν + η * φ ξ) :
    Tendsto (fun N => expect (G N) f) atTop (𝓝 ((∫ ξ, f ξ ∂(F : Measure ↥Ξ) : ℝ) : EReal)) := by
  set ψ : ↥Ξ → ℝ := fun ξ => (φ ξ : ℝ) with hψdef
  have hψc : Continuous ψ := NNReal.continuous_coe.comp hφc
  have hfint : ∀ μ : Measure ↥Ξ, [IsFiniteMeasure μ] → Integrable ψ μ → Integrable f μ := by
    intro μ _ hψ
    refine Integrable.mono' ((integrable_const ν).add (hψ.const_mul η))
      hf.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]; exact hb ξ
  have hevfin := hφconv.eventually (gt_mem_nhds hφF)
  have hψF : Integrable ψ (F : Measure ↥Ξ) := integrable_of_lintegral hφc hφF
  have hψconv : Tendsto (fun N => ∫ ξ, ψ ξ ∂(G N : Measure ↥Ξ)) atTop
      (𝓝 (∫ ξ, ψ ξ ∂(F : Measure ↥Ξ))) := by
    rw [integral_eq_lintegral hφc]
    refine ((ENNReal.tendsto_toReal hφF.ne).comp hφconv).congr' ?_
    exact Eventually.of_forall fun N => (integral_eq_lintegral hφc).symm
  -- tails
  set τ : ℕ → ↥Ξ → ℝ := fun n ξ => ψ ξ - trunc φ hφc n ξ with hτdef
  have htrunc_apply : ∀ n ξ, trunc φ hφc n ξ = min (ψ ξ) n := fun n ξ => rfl
  have hτint : ∀ (μ : Measure ↥Ξ) [IsFiniteMeasure μ], Integrable ψ μ → ∀ n,
      Integrable (τ n) μ := fun μ _ hψ n => hψ.sub ((trunc φ hφc n).integrable μ)
  have hτconv : ∀ n, Tendsto (fun N => ∫ ξ, τ n ξ ∂(G N : Measure ↥Ξ)) atTop
      (𝓝 (∫ ξ, τ n ξ ∂(F : Measure ↥Ξ))) := by
    intro n
    have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hGF) (trunc φ hφc n)
    rw [integral_sub hψF ((trunc φ hφc n).integrable _)]
    refine (hψconv.sub hw).congr' ?_
    filter_upwards [hevfin] with N hN
    rw [integral_sub (integrable_of_lintegral hφc hN) ((trunc φ hφc n).integrable _)]
  have hτF : Tendsto (fun n : ℕ => ∫ ξ, τ n ξ ∂(F : Measure ↥Ξ)) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := (F : Measure ↥Ξ)) (F := τ)
      (f := fun _ => (0 : ℝ)) ψ (fun n => (hτint _ hψF n).aestronglyMeasurable) hψF
      (fun n => Eventually.of_forall fun ξ => by
        simp only [hτdef, htrunc_apply, Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith [min_le_left (ψ ξ) n])]
        linarith [le_min (NNReal.coe_nonneg (φ ξ)) (Nat.cast_nonneg (α := ℝ) n)])
      (Eventually.of_forall fun ξ => by
        apply tendsto_atTop_of_eventually_const (i₀ := ⌈ψ ξ⌉₊)
        intro n hn
        simp only [hτdef, htrunc_apply]
        rw [min_eq_left ((Nat.le_ceil _).trans (Nat.cast_le.2 hn)), sub_self])
    simpa using this
  -- closeness of `f` to its clamp
  have hclose : ∀ (μ : Measure ↥Ξ) [IsProbabilityMeasure μ], Integrable ψ μ → ∀ n : ℕ,
      |∫ ξ, f ξ ∂μ - ∫ ξ, clamp f hf (ν + η * n) (by positivity) ξ ∂μ| ≤
        η * ∫ ξ, τ n ξ ∂μ := by
    intro μ _ hψ n
    rw [← integral_sub (hfint μ hψ) ((clamp f hf _ _).integrable μ), ← integral_const_mul,
      ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hτint μ hψ n).const_mul η)
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]
    have := clamp_close f hf hν hη φ hb n ξ
    simpa [hτdef, htrunc_apply] using this
  have hreal : Tendsto (fun N => ∫ ξ, f ξ ∂(G N : Measure ↥Ξ)) atTop
      (𝓝 (∫ ξ, f ξ ∂(F : Measure ↥Ξ))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hη1 : 0 < η + 1 := by linarith
    set δ := ε / (8 * (η + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    obtain ⟨n, hn⟩ := (eventually_atTop.1 ((tendsto_order.1 hτF).2 δ hδpos))
    have hn' := hn n le_rfl
    have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hGF)
      (clamp f hf (ν + η * n) (by positivity))
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 ((Metric.tendsto_atTop.1 (hτconv n) δ hδpos |>
      eventually_atTop.2).and ((Metric.tendsto_atTop.1 hw (ε / 4) (by linarith) |>
      eventually_atTop.2).and hevfin))
    refine ⟨N0, fun N hN => ?_⟩
    obtain ⟨hA, hB, hC⟩ := hN0 N hN
    rw [Real.dist_eq] at hA hB ⊢
    have hψG := integrable_of_lintegral hφc hC
    have c1 := hclose (G N : Measure ↥Ξ) hψG n
    have c2 := hclose (F : Measure ↥Ξ) hψF n
    have hτF0 : 0 ≤ ∫ ξ, τ n ξ ∂(F : Measure ↥Ξ) := integral_nonneg fun ξ => by
      show (0 : ℝ) ≤ τ n ξ
      simp only [hτdef, htrunc_apply]; linarith [min_le_left (ψ ξ) n]
    have hηδ : η * δ ≤ ε / 8 := by
      rw [hδ, show η * (ε / (8 * (η + 1))) = ε / 8 * (η / (η + 1)) by field_simp]
      have : η / (η + 1) ≤ 1 := (div_le_one hη1).2 (by linarith)
      nlinarith
    have e1 : η * ∫ ξ, τ n ξ ∂(G N : Measure ↥Ξ) ≤ η * (2 * δ) := by
      apply mul_le_mul_of_nonneg_left _ hη
      rw [abs_lt] at hA; linarith
    have e2 : η * ∫ ξ, τ n ξ ∂(F : Measure ↥Ξ) ≤ η * δ :=
      mul_le_mul_of_nonneg_left hn'.le hη
    rw [abs_lt] at hB
    rw [abs_le] at c1 c2
    rw [abs_lt]
    constructor <;> nlinarith
  -- back to `EReal`
  refine ((continuous_coe_real_ereal.tendsto _).comp hreal).congr' ?_
  filter_upwards [hevfin] with N hN
  simp only [Function.comp, expect]
  rw [if_pos (hfint _ (integrable_of_lintegral hφc hN))]

instance dataLaw_isProb (F : ProbabilityMeasure ↥Ξ) : IsProbabilityMeasure (dataLaw F) := by
  unfold dataLaw; infer_instance

lemma dataLaw_map_eval (F : ProbabilityMeasure ↥Ξ) (i : ℕ) :
    (dataLaw F).map (fun ω => ω i) = (F : Measure ↥Ξ) := by
  unfold dataLaw
  exact Measure.infinitePi_map_eval _ i

/-- Strong law of large numbers for `φ(ξⁱ)`, in the `ℝ≥0∞` form of `sampleMean`. -/
lemma slln_phi (F : ProbabilityMeasure ↥Ξ) {φ : ↥Ξ → ℝ≥0} (hφc : Continuous φ)
    (hφF : ∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(F : Measure ↥Ξ) < ⊤) :
    ∀ᵐ ω ∂(dataLaw F), Tendsto (fun N => sampleMean φ (sample ω N)) atTop
      (𝓝 (∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(F : Measure ↥Ξ))) := by
  have hφm : Measurable (fun ξ => (φ ξ : ℝ)) := (NNReal.continuous_coe.comp hφc).measurable
  set Y : ℕ → (ℕ → ↥Ξ) → ℝ := fun i ω => (φ (ω i) : ℝ) with hY
  have hYm : ∀ i, Measurable (Y i) := fun i => hφm.comp (measurable_pi_apply i)
  have hmap : ∀ i, (dataLaw F).map (Y i) = (F : Measure ↥Ξ).map (fun ξ => (φ ξ : ℝ)) := by
    intro i
    rw [← dataLaw_map_eval F i, Measure.map_map hφm (measurable_pi_apply i)]
    rfl
  have hint : Integrable (Y 0) (dataLaw F) := by
    have h1 : Integrable (fun ξ => (φ ξ : ℝ)) (F : Measure ↥Ξ) := integrable_of_lintegral hφc hφF
    rw [← dataLaw_map_eval F 0] at h1
    exact (integrable_map_measure hφm.aestronglyMeasurable
      (measurable_pi_apply 0).aemeasurable).1 h1
  have hindep : Pairwise (fun i j => ProbabilityTheory.IndepFun (Y i) (Y j) (dataLaw F)) := by
    have := ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => (F : Measure ↥Ξ))
      (X := fun _ ξ => (φ ξ : ℝ)) (fun _ => hφm)
    exact fun i j hij => this.indepFun hij
  have hident : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) (dataLaw F) (dataLaw F) :=
    fun i => ⟨(hYm i).aemeasurable, (hYm 0).aemeasurable, by rw [hmap i, hmap 0]⟩
  have hsl := ProbabilityTheory.strong_law_ae_real Y hint hindep hident
  have hmean : ∫ x, Y 0 x ∂(dataLaw F) = (∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(F : Measure ↥Ξ)).toReal := by
    rw [← integral_eq_lintegral hφc, ← dataLaw_map_eval F 0,
      integral_map (measurable_pi_apply 0).aemeasurable hφm.aestronglyMeasurable]
  filter_upwards [hsl] with ω hω
  rw [hmean] at hω
  have h2 := (ENNReal.continuous_ofReal.tendsto _).comp hω
  rw [ENNReal.ofReal_toReal hφF.ne] at h2
  refine h2.congr' (eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
  simp only [Function.comp, sampleMean, sample, hY]
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hsum : (∑ i ∈ Finset.range N, (φ (ω i) : ℝ)) = ((∑ i ∈ Finset.range N, φ (ω i) : ℝ≥0) : ℝ) := by
    push_cast; rfl
  rw [hsum, show ((N : ℕ) : ℝ) = ((N : ℝ≥0) : ℝ) by simp, ← NNReal.coe_div,
    ENNReal.ofReal_coe_nnreal, ENNReal.coe_div hN0, div_eq_mul_inv, mul_comm,
    Fin.sum_univ_eq_sum_range (fun i => ((φ (ω i) : ℝ≥0) : ℝ≥0∞)), ENNReal.coe_finset_sum]
  simp

end RSAAProp8Aux

open RSAAProp8Aux

theorem solution {d dx : ℕ} {Ξ : Set (Pt d)} (hΞ : IsClosed Ξ) (𝓕 : DUS Ξ)
    (h𝓕 : IsUniformlyConsistent 𝓕) (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx))
    (c : Pt dx → ↥Ξ → ℝ) (hS : Standing F X c) (hA1 : Assumption1 X c)
    (hA3 : Assumption3 F 𝓕 X c) :
    ∀ᵐ ω ∂(dataLaw F), ∀ x ∈ X, ∀ G : ℕ → ProbabilityMeasure ↥Ξ,
      (∀ᶠ N in atTop, G N ∈ 𝓕 N (sample ω N)) →
        Tendsto (fun N => expect (G N) (c x)) atTop (𝓝 ((trueObj F c x : ℝ) : EReal)) := by
  have hweak : ∀ᵐ ω ∂(dataLaw F), ∀ G : ℕ → ProbabilityMeasure ↥Ξ,
      (∀ᶠ N in atTop, G N ∈ 𝓕 N (sample ω N)) → Tendsto G atTop (𝓝 F) := by
    filter_upwards [h𝓕 F] with ω hω G hG
    by_contra h
    obtain ⟨N, h1, h2⟩ := ((hω G h).and_eventually hG).exists
    exact h1 h2
  rcases hA3 with hb | ⟨φ, hφc, hφF, hdev, hφb⟩
  · -- Assumption 3(a): `Ξ` is bounded, hence compact, so `c(x;·)` is bounded
    haveI : CompactSpace ↥Ξ :=
      isCompact_iff_compactSpace.1 (Metric.isCompact_of_isClosed_isBounded hΞ hb)
    filter_upwards [hweak] with ω hω x hx G hG
    set f : ↥Ξ →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨c x, (hS.2 x hx).2⟩
    have := ui_conv (hω G hG) (φ := fun _ => 0) continuous_const (by simp)
      (by simp) (hS.2 x hx).2 (norm_nonneg f) le_rfl (fun ξ => by
        have := f.norm_coe_le_norm ξ
        simpa [Real.norm_eq_abs, f] using this)
    exact this
  · -- Assumption 3(b): convergence of the `φ`-moments, then uniform integrability
    filter_upwards [hweak, hdev, slln_phi F hφc hφF] with ω hω hdω hsl x hx G hG
    obtain ⟨ν, η, hνη⟩ := hφb x hx
    have hb' : ∀ ξ, |c x ξ| ≤ |ν| + |η| * φ ξ := fun ξ =>
      (hνη ξ).trans (add_le_add (le_abs_self ν)
        (mul_le_mul_of_nonneg_right (le_abs_self η) (NNReal.coe_nonneg _)))
    -- the deviation along `G` tends to zero
    set e : ℕ → ℝ≥0∞ := fun N => phiDev φ (G N) (sample ω N) with he
    have he0 : Tendsto e atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdω
        (Eventually.of_forall fun N => zero_le) ?_
      filter_upwards [hG] with N hN
      exact le_iSup₂ (f := fun G' (_ : G' ∈ 𝓕 N (sample ω N)) => phiDev φ G' (sample ω N))
        (G N) hN
    set a : ℕ → ℝ≥0∞ := fun N => ∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(G N : Measure ↥Ξ) with ha
    set b : ℕ → ℝ≥0∞ := fun N => sampleMean φ (sample ω N) with hbdef
    have hup : ∀ N, a N ≤ b N + e N := fun N => by
      simp only [ha, hbdef, he, phiDev]
      calc _ ≤ sampleMean φ (sample ω N) +
            (∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(G N : Measure ↥Ξ) - sampleMean φ (sample ω N)) :=
            le_add_tsub
        _ ≤ _ := by gcongr; exact le_self_add
    have hlo : ∀ N, b N - e N ≤ a N := fun N => by
      rw [tsub_le_iff_right]
      simp only [ha, hbdef, he, phiDev]
      calc _ ≤ ∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(G N : Measure ↥Ξ) +
            (sampleMean φ (sample ω N) - ∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(G N : Measure ↥Ξ)) :=
            le_add_tsub
        _ ≤ _ := by gcongr; exact le_add_self
    have hconv : Tendsto a atTop (𝓝 (∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(F : Measure ↥Ξ))) := by
      have h1 : Tendsto (fun N => b N + e N) atTop
          (𝓝 (∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(F : Measure ↥Ξ))) := by
        simpa using hsl.add he0
      have h2 : Tendsto (fun N => b N - e N) atTop
          (𝓝 (∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(F : Measure ↥Ξ))) := by
        simpa using ENNReal.Tendsto.sub hsl he0 (Or.inl hφF.ne)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le h2 h1 hlo hup
    exact ui_conv (hω G hG) hφc hφF hconv (hS.2 x hx).2 (abs_nonneg ν) (abs_nonneg η) hb'
