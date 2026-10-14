-- Prove2me | solution 1 for TPG.lemma_4_ideal_hac_consistency
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T05:12:59.292553+00:00
-- url     : https://prove2.me/submissions/c93c1bfd-3ab3-4276-a308-c0fb29c9a3ab

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference
import Theorems.Thm_TPG_lemma_1_covariance_inequality
import Theorems.Thm_TPG_lemma_2_alpha_mixing
import Theorems.Thm_TPG_isProbabilityMeasure_trajLaw
import Theorems.Thm_TPG_ae_abs_Y_le

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open TPG

namespace HAC4

/-! ### General helper lemmas -/

/-- A finite sum of values of a nonnegative summable sequence along an injective reindexing is
bounded by the full series. -/
lemma sum_ite_le_tsum {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) (F : Finset ℕ)
    (p : ℕ → Prop) [DecidablePred p] (e : ℕ → ℕ)
    (he : ∀ x ∈ F, ∀ y ∈ F, p x → p y → e x = e y → x = y) :
    ∑ s ∈ F, (if p s then g (e s) else 0) ≤ ∑' n, g n := by
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn e (F.filter p : Set ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact he x hx.1 y hy.1 hx.2 hy.2 hxy
  rw [← Finset.sum_image hinj]
  exact hg.sum_le_tsum _ (fun i _ => hg0 i)

section Var

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

lemma two_cov_le [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    2 * cov[X, Y; μ] ≤ Var[X; μ] + Var[Y; μ] := by
  have h := variance_nonneg (X - Y) μ
  rw [variance_sub hX hY] at h
  linarith

lemma variance_add_le [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[fun ω => X ω + Y ω; μ] ≤ 2 * Var[X; μ] + 2 * Var[Y; μ] := by
  rw [variance_fun_add hX hY]
  have := two_cov_le hX hY
  linarith

lemma variance_sum_le [IsFiniteMeasure μ] {ι : Type} (s : Finset ι) {X : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    Var[fun ω => ∑ i ∈ s, X i ω; μ] ≤ (s.card : ℝ) * ∑ i ∈ s, Var[X i; μ] := by
  rw [variance_fun_sum' hX]
  calc ∑ i ∈ s, ∑ j ∈ s, cov[X i, X j; μ]
      ≤ ∑ i ∈ s, ∑ j ∈ s, (Var[X i; μ] + Var[X j; μ]) / 2 := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
        have := two_cov_le (hX i hi) (hX j hj)
        linarith
    _ = (s.card : ℝ) * ∑ i ∈ s, Var[X i; μ] := by
        simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
        ring

lemma memTop_mul {f g : Ω → ℝ} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    MemLp (fun ω => f ω * g ω) ⊤ μ := hg.mul' hf

lemma memTop_two [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f ⊤ μ) : MemLp f 2 μ :=
  hf.mono_exponent le_top

lemma memTop_int [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f ⊤ μ) : Integrable f μ :=
  memLp_one_iff_integrable.1 (hf.mono_exponent le_top)

lemma ae_abs_mul_le {f g : Ω → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hf : ∀ᵐ ω ∂μ, |f ω| ≤ a)
    (hg : ∀ᵐ ω ∂μ, |g ω| ≤ b) : ∀ᵐ ω ∂μ, |f ω * g ω| ≤ a * b := by
  filter_upwards [hf, hg] with ω h1 h2
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ha

end Var

/-! ### The mixing profile -/

/-- The summable profile `(d + 1) γ^{max(0, d - k - 1)}`. -/
noncomputable def bSeq (γ : ℝ) (k d : ℕ) : ℝ := ((d : ℝ) + 1) * γ ^ (d - (k + 1))

/-- The constant `∑_d (d + 1) γ^{max(0, d - k - 1)}`. -/
noncomputable def Sc (γ : ℝ) (k : ℕ) : ℝ := ∑' d, bSeq γ k d

lemma bSeq_nonneg {γ : ℝ} (hγ0 : 0 < γ) (k d : ℕ) : 0 ≤ bSeq γ k d := by
  unfold bSeq; positivity

lemma pow_le_bSeq {γ : ℝ} (hγ0 : 0 < γ) (k d : ℕ) : γ ^ (d - (k + 1)) ≤ bSeq γ k d := by
  unfold bSeq
  have h1 : 0 ≤ γ ^ (d - (k + 1)) := by positivity
  have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

lemma mul_pow_le_bSeq {γ : ℝ} (hγ0 : 0 < γ) (k d : ℕ) :
    (d : ℝ) * γ ^ (d - (k + 1)) ≤ bSeq γ k d := by
  unfold bSeq
  have h1 : 0 ≤ γ ^ (d - (k + 1)) := by positivity
  nlinarith

lemma bSeq_summable {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (k : ℕ) : Summable (bSeq γ k) := by
  rw [← summable_nat_add_iff (k + 1)]
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * γ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1
      (by rw [Real.norm_eq_abs, abs_of_pos hγ0]; exact hγ1)
  have h2 : Summable (fun n : ℕ => ((k : ℝ) + 2) * γ ^ n) :=
    (summable_geometric_of_lt_one hγ0.le hγ1).mul_left _
  have h3 : (fun n : ℕ => bSeq γ k (n + (k + 1)))
      = fun n : ℕ => (n : ℝ) ^ 1 * γ ^ n + ((k : ℝ) + 2) * γ ^ n := by
    funext n
    unfold bSeq
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  rw [h3]
  exact h1.add h2

lemma Sc_nonneg {γ : ℝ} (hγ0 : 0 < γ) (k : ℕ) : 0 ≤ Sc γ k :=
  tsum_nonneg (bSeq_nonneg hγ0 k)

/-! ### Abstract setting: a bounded centred sequence with mixing-type moment bounds -/

/-- Hypotheses on a sequence `V` used in the consistency argument. -/
structure MixHyp {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (V : ℕ → Ω → ℝ) (K γ : ℝ)
    (T k : ℕ) : Prop where
  γ0 : 0 < γ
  γ1 : γ < 1
  K0 : 0 ≤ K
  meas : ∀ t, Measurable (V t)
  bd : ∀ t, ∀ᵐ ω ∂μ, |V t ω| ≤ K
  mean : ∀ t, ∫ ω, V t ω ∂μ = 0
  two : ∀ t s, t ≤ s → s < T →
    |∫ ω, V t ω * V s ω ∂μ| ≤ 4 * K ^ 2 * γ ^ (s - t - (k + 1))
  fourA : ∀ t s ℓ, t + ℓ ≤ s → s + ℓ < T →
    |cov[fun ω => V t ω * V (t + ℓ) ω, fun ω => V s ω * V (s + ℓ) ω; μ]|
      ≤ 4 * K ^ 4 * γ ^ (s - (t + ℓ) - (k + 1))
  fourB : ∀ t s ℓ, t ≤ s → s ≤ t + ℓ → s + ℓ < T →
    |∫ ω, (V t ω * V (t + ℓ) ω) * (V s ω * V (s + ℓ) ω) ∂μ|
      ≤ 4 * K ^ 4 * γ ^ (s - t - (k + 1))

/-- Lag-`ℓ` autocovariance of the sequence `V` over the horizon `T`. -/
noncomputable def gam {Ω : Type} (V : ℕ → Ω → ℝ) (T ℓ : ℕ) (ω : Ω) : ℝ :=
  (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T,
    if t + ℓ = s then V t ω * V s ω else 0

/-- Bartlett-weighted sum of the autocovariances. -/
noncomputable def hac {Ω : Type} (V : ℕ → Ω → ℝ) (T L : ℕ) (ω : Ω) : ℝ :=
  gam V T 0 ω + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * gam V T ℓ ω

section Abstract

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {V : ℕ → Ω → ℝ} {K γ : ℝ}
  {T k : ℕ}

lemma gam_eq (V : ℕ → Ω → ℝ) (T ℓ : ℕ) (ω : Ω) :
    gam V T ℓ ω = (1 / (T : ℝ)) * ∑ t ∈ Finset.range (T - ℓ), V t ω * V (t + ℓ) ω := by
  unfold gam
  congr 1
  have h1 : ∀ t ∈ Finset.range T,
      (∑ s ∈ Finset.range T, if t + ℓ = s then V t ω * V s ω else 0)
        = if t + ℓ < T then V t ω * V (t + ℓ) ω else 0 := by
    intro t _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma MixHyp.memTop (h : MixHyp μ V K γ T k) (t : ℕ) : MemLp (V t) ⊤ μ :=
  memLp_top_of_bound (h.meas t).aestronglyMeasurable K
    ((h.bd t).mono fun ω hω => by rwa [Real.norm_eq_abs])

lemma gam_memTop (h : MixHyp μ V K γ T k) (ℓ : ℕ) : MemLp (gam V T ℓ) ⊤ μ := by
  rw [show gam V T ℓ = fun ω => (1 / (T : ℝ)) * ∑ t ∈ Finset.range (T - ℓ), V t ω * V (t + ℓ) ω
    from funext (gam_eq V T ℓ)]
  exact (memLp_finsetSum _ fun t _ => memTop_mul (h.memTop t) (h.memTop _)).const_mul _

lemma hac_memTop (h : MixHyp μ V K γ T k) (L : ℕ) : MemLp (hac V T L) ⊤ μ := by
  have hfun : hac V T L
      = fun ω => gam V T 0 ω + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * gam V T ℓ ω := rfl
  rw [hfun]
  exact (gam_memTop h 0).add
    ((memLp_finsetSum _ fun ℓ _ => (gam_memTop h ℓ).const_mul _).const_mul 2)

variable [IsProbabilityMeasure μ]

lemma cov_U_le_of_le (h : MixHyp μ V K γ T k) {t s ℓ : ℕ} (hts : t ≤ s) (hs : s + ℓ < T) :
    |cov[fun ω => V t ω * V (t + ℓ) ω, fun ω => V s ω * V (s + ℓ) ω; μ]|
      ≤ 20 * K ^ 4 * ((if t + ℓ ≤ s then bSeq γ k (s - (t + ℓ)) else 0) + bSeq γ k (s - t)) := by
  have hγ0 := h.γ0
  have hK4 : 0 ≤ K ^ 4 := by positivity
  have hK2 : 0 ≤ K ^ 2 := by positivity
  have hb0 : ∀ d, 0 ≤ bSeq γ k d := bSeq_nonneg hγ0 k
  by_cases hc : t + ℓ ≤ s
  · rw [if_pos hc]
    have h1 := h.fourA t s ℓ hc hs
    have h2 := pow_le_bSeq hγ0 k (s - (t + ℓ))
    have h3 := hb0 (s - t)
    calc _ ≤ 4 * K ^ 4 * γ ^ (s - (t + ℓ) - (k + 1)) := h1
      _ ≤ 20 * K ^ 4 * bSeq γ k (s - (t + ℓ)) := by nlinarith [mul_nonneg hK4 (hb0 (s - (t + ℓ)))]
      _ ≤ 20 * K ^ 4 * (bSeq γ k (s - (t + ℓ)) + bSeq γ k (s - t)) := by
        nlinarith [mul_nonneg hK4 h3]
  · rw [if_neg hc, zero_add]
    have hU1 : MemLp (fun ω => V t ω * V (t + ℓ) ω) 2 μ :=
      memTop_two (memTop_mul (h.memTop t) (h.memTop _))
    have hU2 : MemLp (fun ω => V s ω * V (s + ℓ) ω) 2 μ :=
      memTop_two (memTop_mul (h.memTop s) (h.memTop _))
    rw [covariance_eq_sub hU1 hU2]
    have e1 : |∫ ω, (V t ω * V (t + ℓ) ω) * (V s ω * V (s + ℓ) ω) ∂μ|
        ≤ 4 * K ^ 4 * γ ^ (s - t - (k + 1)) := h.fourB t s ℓ hts (by omega) hs
    have e2 : |∫ ω, V t ω * V (t + ℓ) ω ∂μ| ≤ 4 * K ^ 2 * γ ^ (ℓ - (k + 1)) := by
      have := h.two t (t + ℓ) (by omega) (by omega)
      rwa [Nat.add_sub_cancel_left] at this
    have e3 : |∫ ω, V s ω * V (s + ℓ) ω ∂μ| ≤ 4 * K ^ 2 * γ ^ (ℓ - (k + 1)) := by
      have := h.two s (s + ℓ) (by omega) hs
      rwa [Nat.add_sub_cancel_left] at this
    have m1 : γ ^ (ℓ - (k + 1)) ≤ γ ^ (s - t - (k + 1)) :=
      pow_le_pow_of_le_one hγ0.le h.γ1.le (by omega)
    have m2 : γ ^ (ℓ - (k + 1)) ≤ 1 := pow_le_one₀ hγ0.le h.γ1.le
    have m0 : 0 ≤ γ ^ (ℓ - (k + 1)) := by positivity
    set A := ∫ ω, (V t ω * V (t + ℓ) ω) * (V s ω * V (s + ℓ) ω) ∂μ with hA
    set B := ∫ ω, V t ω * V (t + ℓ) ω ∂μ with hB
    set C := ∫ ω, V s ω * V (s + ℓ) ω ∂μ with hC
    set a' := γ ^ (ℓ - (k + 1)) with ha'
    set a := γ ^ (s - t - (k + 1)) with ha
    have hBC : |B| * |C| ≤ 16 * K ^ 4 * a := by
      calc |B| * |C| ≤ (4 * K ^ 2 * a') * (4 * K ^ 2 * a') :=
            mul_le_mul e2 e3 (abs_nonneg _) (by positivity)
        _ = 16 * K ^ 4 * (a' * a') := by ring
        _ ≤ 16 * K ^ 4 * (a * 1) := by
            have : a' * a' ≤ a * 1 := mul_le_mul m1 m2 m0 (m0.trans m1)
            nlinarith
        _ = 16 * K ^ 4 * a := by ring
    calc |μ[(fun ω => V t ω * V (t + ℓ) ω) * fun ω => V s ω * V (s + ℓ) ω] - B * C|
        = |A - B * C| := rfl
      _ ≤ |A| + |B * C| := abs_sub _ _
      _ = |A| + |B| * |C| := by rw [abs_mul]
      _ ≤ 4 * K ^ 4 * a + 16 * K ^ 4 * a := add_le_add e1 hBC
      _ = 20 * K ^ 4 * a := by ring
      _ ≤ 20 * K ^ 4 * bSeq γ k (s - t) := by
        have := pow_le_bSeq hγ0 k (s - t)
        nlinarith

/-- The pairwise profile bounding the covariances of the lag products. -/
noncomputable def psi (γ : ℝ) (k ℓ t s : ℕ) : ℝ :=
  (if t + ℓ ≤ s then bSeq γ k (s - (t + ℓ)) else 0) + (if t ≤ s then bSeq γ k (s - t) else 0)
    + (if s + ℓ ≤ t then bSeq γ k (t - (s + ℓ)) else 0) + (if s ≤ t then bSeq γ k (t - s) else 0)

lemma cov_U_le (h : MixHyp μ V K γ T k) {t s ℓ : ℕ} (ht : t + ℓ < T) (hs : s + ℓ < T) :
    cov[fun ω => V t ω * V (t + ℓ) ω, fun ω => V s ω * V (s + ℓ) ω; μ]
      ≤ 20 * K ^ 4 * psi γ k ℓ t s := by
  have hK4 : 0 ≤ K ^ 4 := by positivity
  have hb0 : ∀ d, 0 ≤ bSeq γ k d := bSeq_nonneg h.γ0 k
  have i1 : 0 ≤ (if t + ℓ ≤ s then bSeq γ k (s - (t + ℓ)) else 0) := by
    split_ifs
    · exact hb0 _
    · exact le_rfl
  have i2 : 0 ≤ (if t ≤ s then bSeq γ k (s - t) else 0) := by
    split_ifs
    · exact hb0 _
    · exact le_rfl
  have i3 : 0 ≤ (if s + ℓ ≤ t then bSeq γ k (t - (s + ℓ)) else 0) := by
    split_ifs
    · exact hb0 _
    · exact le_rfl
  have i4 : 0 ≤ (if s ≤ t then bSeq γ k (t - s) else 0) := by
    split_ifs
    · exact hb0 _
    · exact le_rfl
  unfold psi
  rcases le_total t s with hts | hst
  · have h1 := (le_abs_self _).trans (cov_U_le_of_le h hts hs)
    rw [if_pos hts]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  · rw [covariance_comm]
    have h1 := (le_abs_self _).trans (cov_U_le_of_le h hst ht)
    rw [if_pos hst]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith

omit [IsProbabilityMeasure μ] in
lemma sum_psi_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (k ℓ t : ℕ) (F : Finset ℕ) :
    ∑ s ∈ F, psi γ k ℓ t s ≤ 4 * Sc γ k := by
  unfold psi
  simp only [Finset.sum_add_distrib]
  have hg0 := bSeq_nonneg hγ0 k
  have hg := bSeq_summable hγ0 hγ1 k
  have h1 := sum_ite_le_tsum hg0 hg F (fun s => t + ℓ ≤ s) (fun s => s - (t + ℓ))
    (by intro x _ y _ hx hy hxy; omega)
  have h2 := sum_ite_le_tsum hg0 hg F (fun s => t ≤ s) (fun s => s - t)
    (by intro x _ y _ hx hy hxy; omega)
  have h3 := sum_ite_le_tsum hg0 hg F (fun s => s + ℓ ≤ t) (fun s => t - (s + ℓ))
    (by intro x _ y _ hx hy hxy; omega)
  have h4 := sum_ite_le_tsum hg0 hg F (fun s => s ≤ t) (fun s => t - s)
    (by intro x _ y _ hx hy hxy; omega)
  unfold Sc
  linarith

lemma var_gam_le (h : MixHyp μ V K γ T k) (hT : 0 < T) (ℓ : ℕ) :
    Var[gam V T ℓ; μ] ≤ 80 * K ^ 4 * Sc γ k / T := by
  have hfun : gam V T ℓ
      = fun ω => (1 / (T : ℝ)) * ∑ t ∈ Finset.range (T - ℓ), V t ω * V (t + ℓ) ω :=
    funext (gam_eq V T ℓ)
  rw [hfun, variance_const_mul]
  have hU : ∀ t ∈ Finset.range (T - ℓ), MemLp (fun ω => V t ω * V (t + ℓ) ω) 2 μ :=
    fun t _ => memTop_two (memTop_mul (h.memTop t) (h.memTop _))
  rw [variance_fun_sum' hU]
  have hK4 : 0 ≤ K ^ 4 := by positivity
  have hS0 : 0 ≤ Sc γ k := Sc_nonneg h.γ0 k
  have hsum : ∑ t ∈ Finset.range (T - ℓ), ∑ s ∈ Finset.range (T - ℓ),
      cov[fun ω => V t ω * V (t + ℓ) ω, fun ω => V s ω * V (s + ℓ) ω; μ]
        ≤ (T : ℝ) * (80 * K ^ 4 * Sc γ k) := by
    calc _ ≤ ∑ t ∈ Finset.range (T - ℓ), ∑ s ∈ Finset.range (T - ℓ),
            20 * K ^ 4 * psi γ k ℓ t s := by
          refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun s hs => ?_
          rw [Finset.mem_range] at ht hs
          exact cov_U_le h (by omega) (by omega)
      _ ≤ ∑ _t ∈ Finset.range (T - ℓ), 80 * K ^ 4 * Sc γ k := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [← Finset.mul_sum]
          have := sum_psi_le h.γ0 h.γ1 k ℓ t (Finset.range (T - ℓ))
          nlinarith
      _ = ((T - ℓ : ℕ) : ℝ) * (80 * K ^ 4 * Sc γ k) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (T : ℝ) * (80 * K ^ 4 * Sc γ k) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Nat.sub_le T ℓ
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  calc (1 / (T : ℝ)) ^ 2 * _ ≤ (1 / (T : ℝ)) ^ 2 * ((T : ℝ) * (80 * K ^ 4 * Sc γ k)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 80 * K ^ 4 * Sc γ k / T := by field_simp

omit [IsProbabilityMeasure μ] in
lemma nw_bounds {L ℓ : ℕ} (hℓ : ℓ ≤ L) : 0 ≤ nwWeight L ℓ ∧ nwWeight L ℓ ≤ 1 := by
  unfold nwWeight
  have hL : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have h1 : (ℓ : ℝ) / ((L : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hL]
    have : (ℓ : ℝ) ≤ L := by exact_mod_cast hℓ
    linarith
  have h2 : 0 ≤ (ℓ : ℝ) / ((L : ℝ) + 1) := by positivity
  constructor <;> linarith

lemma var_hac_le (h : MixHyp μ V K γ T k) (hT : 0 < T) (L : ℕ) :
    Var[hac V T L; μ] ≤ 640 * K ^ 4 * Sc γ k * ((L : ℝ) + 1) ^ 2 / T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hK4 : 0 ≤ K ^ 4 := by positivity
  have hS0 : 0 ≤ Sc γ k := Sc_nonneg h.γ0 k
  set B := 80 * K ^ 4 * Sc γ k / T with hB
  have hB0 : 0 ≤ B := by positivity
  have hg : ∀ ℓ, MemLp (gam V T ℓ) 2 μ := fun ℓ => memTop_two (gam_memTop h ℓ)
  have hterm : ∀ ℓ ∈ Finset.Icc 1 L, MemLp (fun ω => nwWeight L ℓ * gam V T ℓ ω) 2 μ :=
    fun ℓ _ => (hg ℓ).const_mul _
  have hsum2 : MemLp (fun ω => ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * gam V T ℓ ω) 2 μ :=
    memLp_finsetSum _ hterm
  have s1 : Var[fun ω => gam V T 0 ω + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * gam V T ℓ ω; μ]
      ≤ 2 * Var[gam V T 0; μ]
        + 2 * Var[fun ω => 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * gam V T ℓ ω; μ] :=
    variance_add_le (hg 0) (hsum2.const_mul 2)
  have s2 : Var[fun ω => ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * gam V T ℓ ω; μ]
      ≤ (L : ℝ) * ∑ ℓ ∈ Finset.Icc 1 L, Var[fun ω => nwWeight L ℓ * gam V T ℓ ω; μ] := by
    have := variance_sum_le (μ := μ) (Finset.Icc 1 L)
      (X := fun ℓ ω => nwWeight L ℓ * gam V T ℓ ω) hterm
    simpa [Nat.card_Icc] using this
  have s3 : ∑ ℓ ∈ Finset.Icc 1 L, Var[fun ω => nwWeight L ℓ * gam V T ℓ ω; μ] ≤ (L : ℝ) * B := by
    calc _ ≤ ∑ _ℓ ∈ Finset.Icc 1 L, B := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          rw [variance_const_mul]
          have hw := nw_bounds (Finset.mem_Icc.1 hℓ).2
          have hv := var_gam_le h hT ℓ
          have hv0 := variance_nonneg (gam V T ℓ) μ
          have hw2 : nwWeight L ℓ ^ 2 ≤ 1 := by nlinarith [hw.1, hw.2]
          calc nwWeight L ℓ ^ 2 * Var[gam V T ℓ; μ] ≤ 1 * Var[gam V T ℓ; μ] :=
                mul_le_mul_of_nonneg_right hw2 hv0
            _ ≤ B := by rw [one_mul]; exact hv
      _ = (L : ℝ) * B := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          simp
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  calc Var[hac V T L; μ]
      = Var[fun ω => gam V T 0 ω + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * gam V T ℓ ω; μ] := rfl
    _ ≤ 2 * Var[gam V T 0; μ]
        + 2 * Var[fun ω => 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * gam V T ℓ ω; μ] := s1
    _ = 2 * Var[gam V T 0; μ]
        + 8 * Var[fun ω => ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * gam V T ℓ ω; μ] := by
        rw [variance_const_mul]; ring
    _ ≤ 2 * B + 8 * ((L : ℝ) * ((L : ℝ) * B)) := by
        have h0 := var_gam_le h hT 0
        have h1 : Var[fun ω => ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * gam V T ℓ ω; μ]
            ≤ (L : ℝ) * ((L : ℝ) * B) := s2.trans (mul_le_mul_of_nonneg_left s3 hL0)
        linarith
    _ ≤ 8 * ((L : ℝ) + 1) ^ 2 * B := by nlinarith [mul_nonneg hL0 hB0]
    _ = 640 * K ^ 4 * Sc γ k * ((L : ℝ) + 1) ^ 2 / T := by rw [hB]; ring

lemma integral_gam (h : MixHyp μ V K γ T k) (ℓ : ℕ) :
    ∫ ω, gam V T ℓ ω ∂μ = (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T,
      (if t + ℓ = s then (1 : ℝ) else 0) * ∫ ω, V t ω * V s ω ∂μ := by
  have hpt : ∀ ω, gam V T ℓ ω = (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T,
      (if t + ℓ = s then (1 : ℝ) else 0) * (V t ω * V s ω) := by
    intro ω
    unfold gam
    congr 1
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  have hint : ∀ t s, Integrable
      (fun ω => (if t + ℓ = s then (1 : ℝ) else 0) * (V t ω * V s ω)) μ :=
    fun t s => (memTop_int (memTop_mul (h.memTop t) (h.memTop s))).const_mul _
  simp only [hpt]
  rw [integral_const_mul,
    integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun s _ => hint t s))]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_finsetSum _ (fun s _ => hint t s)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul]

omit [IsProbabilityMeasure μ] in
lemma sum_nw (L t s : ℕ) :
    ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * (if t + ℓ = s then (1 : ℝ) else 0)
      = if t < s ∧ s - t ≤ L then nwWeight L (s - t) else 0 := by
  split_ifs with hc
  · rw [Finset.sum_eq_single (s - t)]
    · rw [if_pos (by omega), mul_one]
    · intro b _ hb
      rw [if_neg (by omega), mul_zero]
    · intro hn
      exact absurd (Finset.mem_Icc.2 ⟨by omega, hc.2⟩) hn
  · refine Finset.sum_eq_zero fun ℓ hℓ => ?_
    rw [Finset.mem_Icc] at hℓ
    rw [if_neg (by omega), mul_zero]

/-- Coefficient of `E[V_t V_s]` in the expectation of the weighted sum. -/
noncomputable def cc (L t s : ℕ) : ℝ :=
  (if t + 0 = s then (1 : ℝ) else 0)
    + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * (if t + ℓ = s then (1 : ℝ) else 0)

/-- Coefficient of `E[V_t V_s]` in the variance of the sum, after symmetrization. -/
noncomputable def ee (t s : ℕ) : ℝ :=
  (if t = s then (1 : ℝ) else 0) + 2 * (if t < s then (1 : ℝ) else 0)

omit [IsProbabilityMeasure μ] in
lemma abs_cc_sub_ee (L t s : ℕ) :
    |cc L t s - ee t s| ≤ (if t ≤ s then 2 * ((s - t : ℕ) : ℝ) / ((L : ℝ) + 1) else 0) := by
  have hL : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  unfold cc ee
  rw [sum_nw]
  rcases lt_trichotomy t s with hlt | heq | hgt
  · have c1 : ¬ (t + 0 = s) := by omega
    have c2 : ¬ (t = s) := by omega
    rw [if_neg c1, if_neg c2, if_pos hlt, if_pos hlt.le]
    have hd1 : (1 : ℝ) ≤ ((s - t : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ s - t)
    by_cases hdL : s - t ≤ L
    · rw [if_pos ⟨hlt, hdL⟩]
      unfold nwWeight
      have : (0 : ℝ) + 2 * (1 - ((s - t : ℕ) : ℝ) / ((L : ℝ) + 1)) - (0 + 2 * 1)
          = -(2 * ((s - t : ℕ) : ℝ) / ((L : ℝ) + 1)) := by ring
      rw [this, abs_neg, abs_of_nonneg (by positivity)]
    · have c3 : ¬ (t < s ∧ s - t ≤ L) := fun hh => hdL hh.2
      rw [if_neg c3]
      have hd2 : (L : ℝ) + 1 ≤ ((s - t : ℕ) : ℝ) := by exact_mod_cast (by omega : L + 1 ≤ s - t)
      have : (0 : ℝ) + 2 * 0 - (0 + 2 * 1) = -2 := by ring
      rw [this, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hL]
      linarith
  · subst heq
    have c1 : t + 0 = t := rfl
    have c2 : ¬ (t < t ∧ t - t ≤ L) := fun hh => lt_irrefl t hh.1
    rw [if_pos c1, if_neg c2, if_pos rfl, if_neg (lt_irrefl t), if_pos le_rfl]
    simp
  · have c1 : ¬ (t + 0 = s) := by omega
    have c2 : ¬ (t < s ∧ s - t ≤ L) := fun hh => by omega
    have c3 : ¬ (t = s) := by omega
    have c4 : ¬ (t < s) := by omega
    have c5 : ¬ (t ≤ s) := by omega
    rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5]
    simp

lemma mean_hac_le (h : MixHyp μ V K γ T k) (hT : 0 < T) (L : ℕ) :
    |∫ ω, hac V T L ω ∂μ - (1 / (T : ℝ)) * Var[fun ω => ∑ t ∈ Finset.range T, V t ω; μ]|
      ≤ 8 * K ^ 2 * Sc γ k / ((L : ℝ) + 1) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hL : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hK2 : 0 ≤ K ^ 2 := by positivity
  set R : ℕ → ℕ → ℝ := fun t s => ∫ ω, V t ω * V s ω ∂μ with hR
  have hRsymm : ∀ t s, R t s = R s t := fun t s => by
    simp only [hR]
    exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  -- the variance as a double sum
  have hvar : Var[fun ω => ∑ t ∈ Finset.range T, V t ω; μ]
      = ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, R t s := by
    rw [variance_fun_sum' (fun t _ => memTop_two (h.memTop t))]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
    rw [covariance_eq_sub (memTop_two (h.memTop t)) (memTop_two (h.memTop s)), h.mean t,
      zero_mul, sub_zero]
    rfl
  -- symmetrization of the double sum
  have hsplit : ∀ t s, R t s = (if t = s then (1 : ℝ) else 0) * R t s
      + (if t < s then (1 : ℝ) else 0) * R t s + (if s < t then (1 : ℝ) else 0) * R s t := by
    intro t s
    rcases lt_trichotomy t s with hlt | heq | hgt
    · rw [if_neg (show ¬ t = s by omega), if_pos hlt, if_neg (show ¬ s < t by omega)]; ring
    · subst heq
      rw [if_pos rfl, if_neg (lt_irrefl t)]; ring
    · rw [if_neg (show ¬ t = s by omega), if_neg (show ¬ t < s by omega), if_pos hgt,
        hRsymm t s]
      ring
  have hsym : ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, R t s
      = ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, ee t s * R t s := by
    have hcomm : ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, (if s < t then (1 : ℝ) else 0) * R s t
        = ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, (if t < s then (1 : ℝ) else 0) * R t s :=
      Finset.sum_comm
    calc ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, R t s
        = ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, ((if t = s then (1 : ℝ) else 0) * R t s
            + (if t < s then (1 : ℝ) else 0) * R t s + (if s < t then (1 : ℝ) else 0) * R s t) :=
          Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => hsplit t s
      _ = ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, (if t = s then (1 : ℝ) else 0) * R t s
            + ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, (if t < s then (1 : ℝ) else 0) * R t s
            + ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T,
                (if t < s then (1 : ℝ) else 0) * R t s := by
          simp only [Finset.sum_add_distrib]
          rw [hcomm]
      _ = ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, ee t s * R t s := by
          simp only [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
          unfold ee
          ring
  -- the expectation of the weighted sum as a double sum
  have hgint : ∀ ℓ, Integrable (gam V T ℓ) μ := fun ℓ => memTop_int (gam_memTop h ℓ)
  have hmean : ∫ ω, hac V T L ω ∂μ
      = (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, cc L t s * R t s := by
    have e0 : ∫ ω, hac V T L ω ∂μ = ∫ ω, gam V T 0 ω ∂μ
        + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * ∫ ω, gam V T ℓ ω ∂μ := by
      unfold hac
      rw [integral_add (hgint 0)
        ((integrable_finsetSum _ fun ℓ _ => (hgint ℓ).const_mul _).const_mul _),
        integral_const_mul, integral_finsetSum _ fun ℓ _ => (hgint ℓ).const_mul _]
      simp only [integral_const_mul]
    rw [e0]
    simp only [integral_gam h]
    have hswap : ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * ((1 / (T : ℝ)) *
        ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, (if t + ℓ = s then (1 : ℝ) else 0) * R t s)
        = (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T,
          (∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * (if t + ℓ = s then (1 : ℝ) else 0)) * R t s := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun ℓ _ => ?_
      ring
    rw [hswap, ← mul_assoc, mul_comm 2 (1 / (T : ℝ)), mul_assoc, ← mul_add]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold cc
    ring
  rw [hmean, hvar, hsym, ← mul_sub, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, ← sub_mul]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (T : ℝ))]
  have hterm : ∀ t ∈ Finset.range T, ∀ s ∈ Finset.range T, |(cc L t s - ee t s) * R t s|
      ≤ (8 * K ^ 2 / ((L : ℝ) + 1)) * (if t ≤ s then bSeq γ k (s - t) else 0) := by
    intro t _ s hs
    rw [Finset.mem_range] at hs
    rw [abs_mul]
    have hc := abs_cc_sub_ee L t s
    by_cases hts : t ≤ s
    · rw [if_pos hts] at hc ⊢
      have hR2 : |R t s| ≤ 4 * K ^ 2 * γ ^ (s - t - (k + 1)) := h.two t s hts hs
      have hb := mul_pow_le_bSeq h.γ0 k (s - t)
      have hp0 : 0 ≤ γ ^ (s - t - (k + 1)) := pow_nonneg h.γ0.le _
      calc |cc L t s - ee t s| * |R t s|
          ≤ (2 * ((s - t : ℕ) : ℝ) / ((L : ℝ) + 1)) * (4 * K ^ 2 * γ ^ (s - t - (k + 1))) :=
            mul_le_mul hc hR2 (abs_nonneg _) (by positivity)
        _ = (8 * K ^ 2 / ((L : ℝ) + 1)) * (((s - t : ℕ) : ℝ) * γ ^ (s - t - (k + 1))) := by
            field_simp; ring
        _ ≤ (8 * K ^ 2 / ((L : ℝ) + 1)) * bSeq γ k (s - t) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
    · rw [if_neg hts] at hc ⊢
      have : |cc L t s - ee t s| = 0 := le_antisymm hc (abs_nonneg _)
      rw [this, zero_mul, mul_zero]
  have hS0 : 0 ≤ Sc γ k := Sc_nonneg h.γ0 k
  calc 1 / (T : ℝ) * |∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, (cc L t s - ee t s) * R t s|
      ≤ 1 / (T : ℝ) * ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T,
          (8 * K ^ 2 / ((L : ℝ) + 1)) * (if t ≤ s then bSeq γ k (s - t) else 0) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t ht => ?_)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s hs => hterm t ht s hs)
    _ ≤ 1 / (T : ℝ) * ∑ _t ∈ Finset.range T, (8 * K ^ 2 / ((L : ℝ) + 1)) * Sc γ k := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ?_) (by positivity)
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_ite_le_tsum (bSeq_nonneg h.γ0 k) (bSeq_summable h.γ0 h.γ1 k) _
          (fun s => t ≤ s) (fun s => s - t) (by intro x _ y _ hx hy hxy; omega)
    _ = 8 * K ^ 2 * Sc γ k / ((L : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

end Abstract

/-! ### The trajectory model -/

section Concrete

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma expLaw_prob (E : Env S) (T : ℕ) : IsProbabilityMeasure (E.expLaw T (1 / 2)) := by
  unfold Env.expLaw
  exact isProbabilityMeasure_trajLaw E T (fun _ => 1 / 2) (fun _ => by norm_num)

omit [Fintype S] [MeasurableSingletonClass S] in
lemma sigmaWindow_le (T a b : ℕ) :
    sigmaWindow (S := S) T a b ≤ (inferInstance : MeasurableSpace (Traj S T)) := by
  unfold sigmaWindow
  exact iSup₂_le fun t _ => (measurable_pi_apply t).comap_le

omit [Fintype S] [MeasurableSingletonClass S] in
lemma meas_coord (T a b : ℕ) (t : Fin T) (ha : a ≤ (t : ℕ)) (hb : (t : ℕ) ≤ b) :
    Measurable[sigmaWindow T a b] (fun ω : Traj S T => ω t) := by
  rw [measurable_iff_comap_le]
  unfold sigmaWindow
  exact le_iSup₂_of_le t ⟨ha, hb⟩ le_rfl

lemma abs_ipw (z : Bool) : |ipw z| = 2 := by
  cases z <;> norm_num [ipw]

omit [Fintype S] [MeasurableSingletonClass S] in
/-- `B_t` is a function of the observations at times `t - k, …, t`. -/
lemma meas_Bt (T k : ℕ) (t : Fin T) (a b : ℕ) (ha : a ≤ (t : ℕ) - k) (hb : (t : ℕ) ≤ b) :
    Measurable[sigmaWindow T a b] (fun ω : Traj S T => Bt k t ω) := by
  unfold Bt
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases hc : (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k
  · simp only [if_pos hc]
    have hi : Measurable[sigmaWindow T a b] (fun ω : Traj S T => ω i) :=
      meas_coord T a b i (by omega) (by omega)
    have ht : Measurable[sigmaWindow T a b] (fun ω : Traj S T => ω t) :=
      meas_coord T a b t (by omega) hb
    have hZ : Measurable[sigmaWindow T a b] (fun ω : Traj S T => Z i ω) :=
      (measurable_fst.comp measurable_snd).comp hi
    have hY : Measurable[sigmaWindow T a b] (fun ω : Traj S T => Y t ω) :=
      (measurable_snd.comp measurable_snd).comp ht
    exact ((Measurable.of_discrete (f := ipw)).comp hZ).mul hY
  · simp only [if_neg hc]
    exact measurable_const

lemma card_window_le (T k : ℕ) (t : Fin T) :
    (Finset.univ.filter fun i : Fin T => (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k).card
      ≤ k + 1 := by
  calc _ ≤ (Finset.Icc ((t : ℕ) - k) (t : ℕ)).card := by
        refine Finset.card_le_card_of_injOn (fun i : Fin T => (i : ℕ)) ?_
          (Fin.val_injective.injOn)
        intro i hi
        rw [Finset.mem_coe, Finset.mem_filter] at hi
        change (i : ℕ) ∈ (Finset.Icc ((t : ℕ) - k) (t : ℕ) : Set ℕ)
        rw [Finset.mem_coe, Finset.mem_Icc]
        omega
    _ ≤ k + 1 := by rw [Nat.card_Icc]; omega

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma abs_Bt_le (T k : ℕ) (M : ℝ) (t : Fin T) (ω : Traj S T) (hω : ∀ u : Fin T, |Y u ω| ≤ M) :
    |Bt k t ω| ≤ 2 * ((k : ℝ) + 1) * |M| := by
  unfold Bt
  have hM : |Y t ω| ≤ |M| := (hω t).trans (le_abs_self M)
  calc |∑ i : Fin T, if (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k
          then ipw (Z i ω) * Y t ω else 0|
      ≤ ∑ i : Fin T, |if (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k
          then ipw (Z i ω) * Y t ω else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin T, if (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k then 2 * |M| else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · rw [abs_mul, abs_ipw]; linarith
        · simp
    _ = ((Finset.univ.filter
          fun i : Fin T => (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k).card : ℝ) * (2 * |M|) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k : ℝ) + 1) * (2 * |M|) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_window_le T k t
    _ = 2 * ((k : ℝ) + 1) * |M| := by ring

lemma ae_Bt_le (E : Env S) (T k : ℕ) (M : ℝ) (hM : E.RewardBound M) :
    ∀ᵐ ω ∂(E.expLaw T (1 / 2)), ∀ t : Fin T, |Bt k t ω| ≤ 2 * ((k : ℝ) + 1) * |M| := by
  have h := ae_abs_Y_le E T (fun _ => 1 / 2) M hM
  exact h.mono fun ω hω t => abs_Bt_le T k M t ω hω

omit [Fintype S] [MeasurableSingletonClass S] in
lemma measurable_Bt (T k : ℕ) (t : Fin T) : Measurable (fun ω : Traj S T => Bt k t ω) :=
  (meas_Bt T k t 0 T (Nat.zero_le _) t.2.le).mono (sigmaWindow_le T 0 T) le_rfl

lemma abs_meanB_le (E : Env S) (T k : ℕ) (M : ℝ) (hM : E.RewardBound M) (t : Fin T) :
    |E.meanB T k t| ≤ 2 * ((k : ℝ) + 1) * |M| := by
  have := expLaw_prob E T
  unfold Env.meanB
  have h := norm_integral_le_of_norm_le_const (μ := E.expLaw T (1 / 2))
    (f := fun ω : Traj S T => Bt k t ω) (C := 2 * ((k : ℝ) + 1) * |M|)
    ((ae_Bt_le E T k M hM).mono fun ω hω => by rw [Real.norm_eq_abs]; exact hω t)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at h

/-- The centred summands `V_t = B_t - E[B_t]`, extended by zero to all `t : ℕ`. -/
noncomputable def Vt (E : Env S) (T k : ℕ) (t : ℕ) (ω : Traj S T) : ℝ :=
  if h : t < T then Bt k ⟨t, h⟩ ω - E.meanB T k ⟨t, h⟩ else 0

omit [MeasurableSingletonClass S] in
lemma Vt_of_lt (E : Env S) (T k : ℕ) {t : ℕ} (h : t < T) :
    Vt E T k t = fun ω => Bt k ⟨t, h⟩ ω - E.meanB T k ⟨t, h⟩ := by
  funext ω
  simp only [Vt, dif_pos h]

omit [MeasurableSingletonClass S] in
lemma Vt_of_not_lt (E : Env S) (T k : ℕ) {t : ℕ} (h : ¬ t < T) :
    Vt E T k t = fun _ => 0 := by
  funext ω
  simp only [Vt, dif_neg h]

omit [MeasurableSingletonClass S] in
lemma Vt_fin (E : Env S) (T k : ℕ) (t : Fin T) (ω : Traj S T) :
    Vt E T k (t : ℕ) ω = Bt k t ω - E.meanB T k t := by
  simp only [Vt, dif_pos t.2, Fin.eta]

omit [MeasurableSingletonClass S] in
lemma Vt_meas (E : Env S) (T k : ℕ) (t a b : ℕ) (ha : a ≤ t - k) (hb : t ≤ b) :
    Measurable[sigmaWindow T a b] (Vt E T k t) := by
  by_cases h : t < T
  · rw [Vt_of_lt E T k h]
    exact (meas_Bt T k ⟨t, h⟩ a b ha hb).sub measurable_const
  · rw [Vt_of_not_lt E T k h]
    exact measurable_const

lemma Vt_bd (E : Env S) (T k : ℕ) (M : ℝ) (hM : E.RewardBound M) (t : ℕ) :
    ∀ᵐ ω ∂(E.expLaw T (1 / 2)), |Vt E T k t ω| ≤ 4 * ((k : ℝ) + 1) * |M| := by
  by_cases h : t < T
  · have hm := abs_meanB_le E T k M hM ⟨t, h⟩
    filter_upwards [ae_Bt_le E T k M hM] with ω hω
    have hb := hω ⟨t, h⟩
    have hv : Vt E T k t ω = Bt k ⟨t, h⟩ ω - E.meanB T k ⟨t, h⟩ := by
      simp only [Vt, dif_pos h]
    rw [hv]
    calc |Bt k ⟨t, h⟩ ω - E.meanB T k ⟨t, h⟩|
        ≤ |Bt k ⟨t, h⟩ ω| + |E.meanB T k ⟨t, h⟩| := abs_sub _ _
      _ ≤ 4 * ((k : ℝ) + 1) * |M| := by linarith
  · refine Eventually.of_forall fun ω => ?_
    have hv : Vt E T k t ω = 0 := by simp only [Vt, dif_neg h]
    rw [hv, abs_zero]
    positivity

lemma Vt_mean (E : Env S) (T k : ℕ) (M : ℝ) (hM : E.RewardBound M) (t : ℕ) :
    ∫ ω, Vt E T k t ω ∂(E.expLaw T (1 / 2)) = 0 := by
  have := expLaw_prob E T
  by_cases h : t < T
  · have hint : Integrable (fun ω : Traj S T => Bt k ⟨t, h⟩ ω) (E.expLaw T (1 / 2)) :=
      Integrable.of_bound (measurable_Bt T k ⟨t, h⟩).aestronglyMeasurable
        (2 * ((k : ℝ) + 1) * |M|)
        ((ae_Bt_le E T k M hM).mono fun ω hω => by rw [Real.norm_eq_abs]; exact hω _)
    simp only [Vt_of_lt E T k h]
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
    exact sub_self _
  · simp only [Vt_of_not_lt E T k h, integral_zero]

/-- Covariance bound for bounded functions of two observation windows `[0, s]` and `[u, T]`. -/
lemma window_cov (E : Env S) (T : ℕ) (γ M : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M) (s u : ℕ) (hu : u < T)
    (X Y : Traj S T → ℝ) (hX : Measurable[sigmaWindow T 0 s] X)
    (hY : Measurable[sigmaWindow T u T] Y) (a b : ℝ)
    (hXa : ∀ᵐ ω ∂(E.expLaw T (1 / 2)), |X ω| ≤ a)
    (hYb : ∀ᵐ ω ∂(E.expLaw T (1 / 2)), |Y ω| ≤ b) :
    |cov[X, Y; E.expLaw T (1 / 2)]| ≤ 4 * γ ^ (u - (s + 1)) * a * b := by
  have := expLaw_prob E T
  refine lemma_1_covariance_inequality (E.expLaw T (1 / 2)) (sigmaWindow T 0 s)
    (sigmaWindow T u T) (sigmaWindow_le _ _ _) (sigmaWindow_le _ _ _) X Y hX hY a b _ hXa hYb ?_
  intro A B hA hB
  by_cases hsu : s + 1 ≤ u
  · obtain ⟨h, rfl⟩ : ∃ h, u = s + h + 1 := ⟨u - (s + 1), by omega⟩
    have h2 := lemma_2_alpha_mixing E T (1 / 2) γ M (by norm_num) (by norm_num) hγ0 hγ1 hmix hM
      s h hu A B hA hB
    rwa [show s + h + 1 - (s + 1) = h by omega]
  · rw [show u - (s + 1) = 0 by omega, pow_zero]
    have h1 : 0 ≤ (E.expLaw T (1 / 2)).real (A ∩ B) := measureReal_nonneg
    have h2 : (E.expLaw T (1 / 2)).real (A ∩ B) ≤ 1 := measureReal_le_one
    have h3 : 0 ≤ (E.expLaw T (1 / 2)).real A := measureReal_nonneg
    have h4 : (E.expLaw T (1 / 2)).real A ≤ 1 := measureReal_le_one
    have h5 : 0 ≤ (E.expLaw T (1 / 2)).real B := measureReal_nonneg
    have h6 : (E.expLaw T (1 / 2)).real B ≤ 1 := measureReal_le_one
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg h3 h5, mul_le_one₀ h4 h5 h6]

/-- The centred summands satisfy the abstract hypotheses with `K = 4 (k + 1) |M|`. -/
lemma concrete_mixHyp (E : Env S) (T k : ℕ) (γ M : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M) :
    MixHyp (E.expLaw T (1 / 2)) (Vt E T k) (4 * ((k : ℝ) + 1) * |M|) γ T k := by
  have := expLaw_prob E T
  set K : ℝ := 4 * ((k : ℝ) + 1) * |M| with hK
  have hK0 : 0 ≤ K := by positivity
  have hbd : ∀ t, ∀ᵐ ω ∂(E.expLaw T (1 / 2)), |Vt E T k t ω| ≤ K := Vt_bd E T k M hM
  have hmean : ∀ t, ∫ ω, Vt E T k t ω ∂(E.expLaw T (1 / 2)) = 0 := Vt_mean E T k M hM
  have hmeas : ∀ t, Measurable (Vt E T k t) := fun t =>
    (Vt_meas E T k t 0 t (Nat.zero_le _) le_rfl).mono (sigmaWindow_le T 0 t) le_rfl
  have hmem : ∀ t, MemLp (Vt E T k t) ⊤ (E.expLaw T (1 / 2)) := fun t =>
    memLp_top_of_bound (hmeas t).aestronglyMeasurable K
      ((hbd t).mono fun ω hω => by rwa [Real.norm_eq_abs])
  refine ⟨hγ0, hγ1, hK0, hmeas, hbd, hmean, ?_, ?_, ?_⟩
  · -- two-point bound
    intro t s hts hs
    have hcov := window_cov E T γ M hγ0 hγ1 hmix hM t (s - k) (by omega)
      (Vt E T k t) (Vt E T k s) (Vt_meas E T k t 0 t (Nat.zero_le _) le_rfl)
      (Vt_meas E T k s (s - k) T le_rfl hs.le) K K (hbd t) (hbd s)
    rw [covariance_eq_sub (memTop_two (hmem t)) (memTop_two (hmem s)), hmean t, zero_mul,
      sub_zero, show s - k - (t + 1) = s - t - (k + 1) by omega] at hcov
    calc |∫ ω, Vt E T k t ω * Vt E T k s ω ∂(E.expLaw T (1 / 2))|
        ≤ 4 * γ ^ (s - t - (k + 1)) * K * K := hcov
      _ = 4 * K ^ 2 * γ ^ (s - t - (k + 1)) := by ring
  · -- separated pairs
    intro t s ℓ hts hs
    have hcov := window_cov E T γ M hγ0 hγ1 hmix hM (t + ℓ) (s - k) (by omega)
      (fun ω => Vt E T k t ω * Vt E T k (t + ℓ) ω) (fun ω => Vt E T k s ω * Vt E T k (s + ℓ) ω)
      ((Vt_meas E T k t 0 (t + ℓ) (Nat.zero_le _) (by omega)).mul
        (Vt_meas E T k (t + ℓ) 0 (t + ℓ) (Nat.zero_le _) le_rfl))
      ((Vt_meas E T k s (s - k) T le_rfl (by omega)).mul
        (Vt_meas E T k (s + ℓ) (s - k) T (by omega) (by omega)))
      (K * K) (K * K) (ae_abs_mul_le hK0 (hbd t) (hbd _)) (ae_abs_mul_le hK0 (hbd s) (hbd _))
    rw [show s - k - (t + ℓ + 1) = s - (t + ℓ) - (k + 1) by omega] at hcov
    calc _ ≤ 4 * γ ^ (s - (t + ℓ) - (k + 1)) * (K * K) * (K * K) := hcov
      _ = 4 * K ^ 4 * γ ^ (s - (t + ℓ) - (k + 1)) := by ring
  · -- interlaced pairs: centre the first factor
    intro t s ℓ hts hst hs
    have hY2 : MemLp (fun ω => Vt E T k (t + ℓ) ω * (Vt E T k s ω * Vt E T k (s + ℓ) ω)) 2
        (E.expLaw T (1 / 2)) :=
      memTop_two (memTop_mul (hmem _) (memTop_mul (hmem s) (hmem _)))
    have hcov := window_cov E T γ M hγ0 hγ1 hmix hM t (s - k) (by omega)
      (Vt E T k t) (fun ω => Vt E T k (t + ℓ) ω * (Vt E T k s ω * Vt E T k (s + ℓ) ω))
      (Vt_meas E T k t 0 t (Nat.zero_le _) le_rfl)
      ((Vt_meas E T k (t + ℓ) (s - k) T (by omega) (by omega)).mul
        ((Vt_meas E T k s (s - k) T le_rfl (by omega)).mul
          (Vt_meas E T k (s + ℓ) (s - k) T (by omega) (by omega))))
      K (K * (K * K)) (hbd t)
      (ae_abs_mul_le hK0 (hbd _) (ae_abs_mul_le hK0 (hbd s) (hbd _)))
    rw [covariance_eq_sub (memTop_two (hmem t)) hY2, hmean t, zero_mul, sub_zero,
      show s - k - (t + 1) = s - t - (k + 1) by omega] at hcov
    have hint : ∫ ω, (Vt E T k t ω * Vt E T k (t + ℓ) ω) * (Vt E T k s ω * Vt E T k (s + ℓ) ω)
          ∂(E.expLaw T (1 / 2))
        = ∫ ω, (Vt E T k t * fun ω => Vt E T k (t + ℓ) ω * (Vt E T k s ω * Vt E T k (s + ℓ) ω)) ω
          ∂(E.expLaw T (1 / 2)) :=
      integral_congr_ae (Eventually.of_forall fun ω => by simp only [Pi.mul_apply]; ring)
    rw [hint]
    calc _ ≤ 4 * γ ^ (s - t - (k + 1)) * K * (K * (K * K)) := hcov
      _ = 4 * K ^ 4 * γ ^ (s - t - (k + 1)) := by ring

omit [MeasurableSingletonClass S] in
lemma GammaIdeal_eq (E : Env S) (T k ℓ : ℕ) (ω : Traj S T) :
    E.GammaIdeal T k ℓ ω = gam (Vt E T k) T ℓ ω := by
  unfold Env.GammaIdeal gam
  congr 1
  simp only [← Vt_fin E T k]
  rw [← Fin.sum_univ_eq_sum_range
    (fun t => ∑ s ∈ Finset.range T, if t + ℓ = s then Vt E T k t ω * Vt E T k s ω else 0) T]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Fin.sum_univ_eq_sum_range
    (fun s => if (t : ℕ) + ℓ = s then Vt E T k t ω * Vt E T k s ω else 0) T]

omit [MeasurableSingletonClass S] in
lemma hacIdeal_eq (E : Env S) (T k L : ℕ) : E.hacIdeal T k L = hac (Vt E T k) T L := by
  funext ω
  unfold Env.hacIdeal hac
  simp only [GammaIdeal_eq]

lemma normVar_eq (E : Env S) (T k : ℕ) :
    E.normVar T k = (1 / (T : ℝ)) *
      Var[fun ω => ∑ t ∈ Finset.range T, Vt E T k t ω; E.expLaw T (1 / 2)] := by
  have := expLaw_prob E T
  unfold Env.normVar
  congr 1
  have hpt : (fun ω : Traj S T => ∑ t : Fin T, Bt k t ω)
      = fun ω => (∑ t ∈ Finset.range T, Vt E T k t ω) + ∑ t : Fin T, E.meanB T k t := by
    funext ω
    rw [← Fin.sum_univ_eq_sum_range (fun t => Vt E T k t ω) T, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Vt_fin]
    ring
  rw [hpt, variance_add_const]
  refine (Finset.measurable_sum _ fun t _ => ?_).aestronglyMeasurable
  exact (Vt_meas E T k t 0 t (Nat.zero_le _) le_rfl).mono (sigmaWindow_le T 0 t) le_rfl

end Concrete

/-! ### Elementary limits -/

lemma tendsto_bandwidth_ratio (L : ℕ → ℕ) (hL : IsBandwidth L) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun T : ℕ => C * ((L T : ℝ) + 1) ^ 2 / T) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := hL.2.2.bound
  have hlim : Tendsto (fun T : ℕ => C * (|c| + 1) ^ 2 / (T : ℝ) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero' (Eventually.of_forall fun T => by positivity) ?_ hlim
  filter_upwards [hc, eventually_ge_atTop 1] with T hT hT1
  have hT1' : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  set x : ℝ := (T : ℝ) ^ ((1 : ℝ) / 3) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow hT1' (by norm_num)
  have hx0 : 0 < x := by linarith
  have hx3 : x ^ 3 = T := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg T)]
    norm_num
  have hLx : (L T : ℝ) ≤ c * x := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hx0.le] at hT
    exact hT
  have hL1 : (L T : ℝ) + 1 ≤ (|c| + 1) * x := by
    have := le_abs_self c
    nlinarith
  have hL0 : (0 : ℝ) ≤ (L T : ℝ) + 1 := by positivity
  have hsq : ((L T : ℝ) + 1) ^ 2 ≤ ((|c| + 1) * x) ^ 2 := by
    apply pow_le_pow_left₀ hL0 hL1
  have hTpos : (0 : ℝ) < T := by linarith
  rw [div_le_div_iff₀ hTpos hx0]
  calc C * ((L T : ℝ) + 1) ^ 2 * x ≤ C * ((|c| + 1) * x) ^ 2 * x := by
        apply mul_le_mul_of_nonneg_right _ hx0.le
        exact mul_le_mul_of_nonneg_left hsq hC
    _ = C * (|c| + 1) ^ 2 * x ^ 3 := by ring
    _ = C * (|c| + 1) ^ 2 * T := by rw [hx3]

end HAC4

open HAC4 in
theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M v : ℝ) (L : ℕ → ℕ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M)
    (hvar : E.AsymptoticVariance k v) (hL : IsBandwidth L) :
    E.TendstoInProb (fun (T : ℕ) (ω : Traj S T) => E.hacIdeal T k (L T) ω) v := by
  intro ε hε
  show Tendsto (fun T : ℕ => (E.expLaw T (1 / 2)) {ω | ε ≤ |E.hacIdeal T k (L T) ω - v|})
    atTop (𝓝 0)
  set K : ℝ := 4 * ((k : ℝ) + 1) * |M| with hK
  set Sg : ℝ := Sc γ k with hSg
  have hS0 : 0 ≤ Sg := Sc_nonneg hγ0 k
  have hMH : ∀ T, MixHyp (E.expLaw T (1 / 2)) (Vt E T k) K γ T k :=
    fun T => concrete_mixHyp E T k γ M hγ0 hγ1 (hmix T) hM
  -- bias and variance bounds at a fixed horizon
  have hmeanb : ∀ T, 0 < T →
      |∫ ω, E.hacIdeal T k (L T) ω ∂(E.expLaw T (1 / 2)) - E.normVar T k|
        ≤ 8 * K ^ 2 * Sg / ((L T : ℝ) + 1) := by
    intro T hT
    have := expLaw_prob E T
    rw [hacIdeal_eq, normVar_eq]
    exact mean_hac_le (hMH T) hT (L T)
  have hvarb : ∀ T, 0 < T → Var[E.hacIdeal T k (L T); E.expLaw T (1 / 2)]
      ≤ 640 * K ^ 4 * Sg * ((L T : ℝ) + 1) ^ 2 / T := by
    intro T hT
    have := expLaw_prob E T
    rw [hacIdeal_eq]
    exact var_hac_le (hMH T) hT (L T)
  have hmem : ∀ T, MemLp (E.hacIdeal T k (L T)) 2 (E.expLaw T (1 / 2)) := by
    intro T
    have := expLaw_prob E T
    rw [hacIdeal_eq]
    exact memTop_two (hac_memTop (hMH T) (L T))
  -- limits
  have hLtop : Tendsto (fun T : ℕ => (L T : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hL.2.1)
  have h1 : Tendsto (fun T : ℕ => 8 * K ^ 2 * Sg / ((L T : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hLtop
  have h2 : Tendsto (fun T : ℕ => 640 * K ^ 4 * Sg / (ε / 2) ^ 2 * ((L T : ℝ) + 1) ^ 2 / T)
      atTop (𝓝 0) :=
    tendsto_bandwidth_ratio L hL _ (by positivity)
  have hev1 : ∀ᶠ T : ℕ in atTop, 8 * K ^ 2 * Sg / ((L T : ℝ) + 1) < ε / 4 :=
    (tendsto_order.1 h1).2 _ (by positivity)
  have hev3 : ∀ᶠ T : ℕ in atTop, |E.normVar T k - v| < ε / 4 := by
    have := (Metric.tendsto_nhds.1 hvar.2) (ε / 4) (by positivity)
    simpa [Real.dist_eq] using this
  have hev : ∀ᶠ T : ℕ in atTop,
      (E.expLaw T (1 / 2)) {ω | ε ≤ |E.hacIdeal T k (L T) ω - v|}
        ≤ ENNReal.ofReal (640 * K ^ 4 * Sg / (ε / 2) ^ 2 * ((L T : ℝ) + 1) ^ 2 / T) := by
    filter_upwards [hev1, hev3, eventually_gt_atTop 0] with T hT1 hT3 hTpos
    have := expLaw_prob E T
    have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
    set m : ℝ := ∫ ω, E.hacIdeal T k (L T) ω ∂(E.expLaw T (1 / 2)) with hm
    have hmv : |m - v| ≤ ε / 2 := by
      have hb := hmeanb T hTpos
      calc |m - v| ≤ |m - E.normVar T k| + |E.normVar T k - v| := abs_sub_le _ _ _
        _ ≤ ε / 2 := by linarith
    have hsub : {ω | ε ≤ |E.hacIdeal T k (L T) ω - v|}
        ⊆ {ω | ε / 2 ≤ |E.hacIdeal T k (L T) ω - m|} := by
      intro ω hω
      have hω' : ε ≤ |E.hacIdeal T k (L T) ω - v| := hω
      show ε / 2 ≤ |E.hacIdeal T k (L T) ω - m|
      have := abs_sub_le (E.hacIdeal T k (L T) ω) m v
      linarith
    calc (E.expLaw T (1 / 2)) {ω | ε ≤ |E.hacIdeal T k (L T) ω - v|}
        ≤ (E.expLaw T (1 / 2)) {ω | ε / 2 ≤ |E.hacIdeal T k (L T) ω - m|} := measure_mono hsub
      _ ≤ ENNReal.ofReal (Var[E.hacIdeal T k (L T); E.expLaw T (1 / 2)] / (ε / 2) ^ 2) :=
          meas_ge_le_variance_div_sq (hmem T) (by positivity)
      _ ≤ ENNReal.ofReal (640 * K ^ 4 * Sg / (ε / 2) ^ 2 * ((L T : ℝ) + 1) ^ 2 / T) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hb := hvarb T hTpos
          have hε2 : (0 : ℝ) < (ε / 2) ^ 2 := by positivity
          calc Var[E.hacIdeal T k (L T); E.expLaw T (1 / 2)] / (ε / 2) ^ 2
              ≤ (640 * K ^ 4 * Sg * ((L T : ℝ) + 1) ^ 2 / T) / (ε / 2) ^ 2 :=
                div_le_div_of_nonneg_right hb hε2.le
            _ = 640 * K ^ 4 * Sg / (ε / 2) ^ 2 * ((L T : ℝ) + 1) ^ 2 / T := by
                field_simp
  have h2' : Tendsto (fun T : ℕ =>
      ENNReal.ofReal (640 * K ^ 4 * Sg / (ε / 2) ^ 2 * ((L T : ℝ) + 1) ^ 2 / T)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp h2
    rw [ENNReal.ofReal_zero] at h
    exact h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2'
    (Eventually.of_forall fun _ => bot_le) hev
