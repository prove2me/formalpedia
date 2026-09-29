-- Prove2me | solution 1 for PolyakJuditsky.Averaging.lemma2_representation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:52:27.184523+00:00
-- url     : https://prove2.me/submissions/df847544-213f-4e9a-99d9-f18682043405

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open Filter Topology

namespace PolyakJuditsky.Averaging

open scoped Matrix.Norms.L2Operator in
theorem aux_pj_real_le_complex {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    matNorm M ≤ ‖M.map (algebraMap ℝ ℂ)‖ := by
  unfold matNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
  set vc : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (fun i => ((v i : ℝ) : ℂ)) with hvc
  have h1 : ‖vc‖ = ‖v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [vc]
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M v‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M.map (algebraMap ℝ ℂ)) vc‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := RingHom.map_mulVec (algebraMap ℝ ℂ) M (WithLp.ofLp v) i
    simp only [vc, Matrix.toEuclideanCLM_toLp]
    rw [Matrix.ofLp_toEuclideanCLM]
    have e : (fun i => ((v.ofLp i : ℝ) : ℂ)) = (⇑(algebraMap ℝ ℂ) ∘ v.ofLp) := rfl
    rw [e, ← this]
    simp
  rw [h2, ← h1, Matrix.cstar_norm_def]
  exact ContinuousLinearMap.le_opNorm _ _


open scoped Matrix.Norms.L2Operator in
theorem aux_pj_spec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : EigenRePos A) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      matNorm ((1 - ε • A) ^ n) ≤ q ^ n := by
  set Ac := A.map (algebraMap ℝ ℂ) with hAc
  have hcomp : IsCompact (spectrum ℂ Ac) := spectrum.isCompact Ac
  obtain ⟨M0, hM0⟩ := hcomp.exists_bound_of_continuousOn (f := fun z : ℂ => z) continuousOn_id
  obtain ⟨c0, hc0pos, hc0⟩ : ∃ c0 : ℝ, 0 < c0 ∧ ∀ μ ∈ spectrum ℂ Ac, c0 ≤ μ.re := by
    rcases (spectrum ℂ Ac).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨μ0, hμ0, hmin⟩ := hcomp.exists_isMinOn h (Complex.continuous_re.continuousOn)
      exact ⟨μ0.re, hA μ0 hμ0, fun μ hμ => hmin hμ⟩
  set c := min c0 1 with hc
  set M := max M0 1 with hM
  have hcpos : 0 < c := lt_min hc0pos one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  set ε := c / M ^ 2 with hε
  have hεpos : 0 < ε := by positivity
  have hεM : ε * M ^ 2 = c := by rw [hε]; field_simp
  have hεle : ε ≤ c := by
    rw [hε, div_le_iff₀ (by positivity)]
    have : 1 ≤ M ^ 2 := one_le_pow₀ hM1
    nlinarith
  have hεc : ε * c ≤ 1 := by nlinarith
  set q0 := 1 - ε * c / 2 with hq0
  have hq0pos : 0 < q0 := by rw [hq0]; linarith
  have hq0lt : q0 < 1 := by rw [hq0]; nlinarith
  set Bc := (1 - ε • A).map (algebraMap ℝ ℂ) with hBcdef
  have hBc : Bc = 1 - (ε : ℂ) • Ac := by
    ext i j
    simp only [hBcdef, hAc, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hspec : ∀ z ∈ spectrum ℂ Bc, ‖z‖ ≤ q0 := by
    intro z hz
    set μ := (1 - z) / (ε : ℂ) with hμdef
    have hεne : (ε : ℂ) ≠ 0 := by exact_mod_cast hεpos.ne'
    have hεμ : (ε : ℂ) * μ = 1 - z := by rw [hμdef]; field_simp
    have hμ : μ ∈ spectrum ℂ Ac := by
      by_contra hμ
      rw [spectrum.notMem_iff] at hμ
      rw [spectrum.mem_iff] at hz
      apply hz
      have heq : algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) z - Bc =
          algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) (-(ε : ℂ)) *
            (algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) μ - Ac) := by
        rw [hBc, mul_sub, ← map_mul, ← Algebra.smul_def]
        have : -(ε : ℂ) * μ = z - 1 := by rw [neg_mul, hεμ]; ring
        rw [this, map_sub, map_one, neg_smul]
        abel
      rw [heq]
      exact ((Ne.isUnit (neg_ne_zero.mpr hεne)).map _).mul hμ
    have hz' : z = 1 - (ε : ℂ) * μ := by rw [hεμ]; ring
    have hre : c ≤ μ.re := le_trans (min_le_left _ _) (hc0 μ hμ)
    have hnorm : ‖μ‖ ≤ M := le_trans (hM0 μ hμ) (le_max_left _ _)
    have hn2 : ‖μ‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hmu2 : ‖μ‖ ^ 2 = μ.re ^ 2 + μ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hz2 : ‖z‖ ^ 2 = (1 - ε * μ.re) ^ 2 + (ε * μ.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hz']
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
      ring
    have h1 : ε * c ≤ ε * μ.re := mul_le_mul_of_nonneg_left hre hεpos.le
    have h2 : ε ^ 2 * ‖μ‖ ^ 2 ≤ ε ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hn2 (by positivity)
    have hfin : ‖z‖ ^ 2 ≤ q0 ^ 2 := by
      rw [hz2, hq0]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hq0pos.le two_ne_zero).mp hfin
  have hrad : spectralRadius ℂ Bc ≤ ENNReal.ofReal q0 := by
    refine iSup₂_le fun z hz => ?_
    rw [← enorm_eq_nnnorm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hspec z hz)
  set q1 := (1 + q0) / 2 with hq1
  have hq1pos : 0 < q1 := by rw [hq1]; linarith
  have hq1lt : q1 < 1 := by rw [hq1]; linarith
  have hq01 : q0 < q1 := by rw [hq1]; linarith
  have hlt : spectralRadius ℂ Bc < ENNReal.ofReal q1 :=
    lt_of_le_of_lt hrad ((ENNReal.ofReal_lt_ofReal_iff hq1pos).mpr hq01)
  have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius Bc).eventually_lt_const hlt
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨ε, hεpos, q1, hq1pos, hq1lt, n₀ + 1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have h := hn₀ n (by omega)
  rw [ENNReal.ofReal_lt_ofReal_iff hq1pos] at h
  have hpow : (Bc ^ n) = ((1 - ε • A) ^ n).map (algebraMap ℝ ℂ) := by
    rw [hBcdef, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
  calc matNorm ((1 - ε • A) ^ n) ≤ ‖((1 - ε • A) ^ n).map (algebraMap ℝ ℂ)‖ :=
        aux_pj_real_le_complex _
    _ = ‖Bc ^ n‖ := by rw [hpow]
    _ = (‖Bc ^ n‖ ^ (1 / n : ℝ)) ^ n := by
        rw [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hn0]
    _ ≤ q1 ^ n := pow_le_pow_left₀ (by positivity) h.le n

theorem aux_pj_X_self {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j : ℕ) :
    lemX A γ j j = 1 := by
  cases j with
  | zero => rfl
  | succ k => simp [lemX]

theorem aux_pj_X_succ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ)
    (h : j ≤ t) : lemX A γ j (t + 1) = (1 - γ t • A) * lemX A γ j t := by
  rw [lemX, if_pos h, sub_mul, one_mul, smul_mul_assoc]

theorem aux_pj_X_shift {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j i : ℕ)
    (h : j ≤ i) : lemX A γ j (i + 1) = lemX A γ (j + 1) (i + 1) * (1 - γ j • A) := by
  induction i, h using Nat.le_induction with
  | base => rw [aux_pj_X_succ A γ j j le_rfl, aux_pj_X_self, aux_pj_X_self, mul_one, one_mul]
  | succ i hi ih =>
    rw [aux_pj_X_succ A γ j (i + 1) (by omega), ih, aux_pj_X_succ A γ (j + 1) (i + 1) (by omega),
      mul_assoc]

theorem aux_pj_alpha_rec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ)
    (h : j + 1 ≤ t) (hγ : γ (j + 1) ≠ 0) :
    lemAlpha A γ j t = γ j • 1 + (γ j / γ (j + 1)) •
      (lemAlpha A γ (j + 1) t * (1 - γ (j + 1) • A)) := by
  unfold lemAlpha
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : j < t), aux_pj_X_self]
  have hs : ∑ i ∈ Finset.Ico (j + 1) t, lemX A γ (j + 1) (i + 1) =
      (∑ i ∈ Finset.Ico (j + 1) t, lemX A γ (j + 1 + 1) (i + 1)) * (1 - γ (j + 1) • A) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    exact aux_pj_X_shift A γ (j + 1) i hi.1
  rw [hs, smul_mul_assoc, smul_smul, div_mul_cancel₀ _ hγ, smul_add]

theorem aux_pj_W_rec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ)
    (h : j + 1 ≤ t) (hγ : γ (j + 1) ≠ 0) (hinv : A⁻¹ * A = 1) :
    lemW A γ j t = (γ j / γ (j + 1)) • (lemW A γ (j + 1) t * (1 - γ (j + 1) • A)) +
      (γ j / γ (j + 1) - 1) • A⁻¹ := by
  unfold lemW
  rw [aux_pj_alpha_rec A γ j t h hγ]
  set c := γ j / γ (j + 1) with hc
  have hcg : c * γ (j + 1) = γ j := by rw [hc, div_mul_cancel₀ _ hγ]
  have e1 : A⁻¹ * (1 - γ (j + 1) • A) = A⁻¹ - γ (j + 1) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    rw [mul_sub, mul_one, mul_smul_comm, hinv]
  rw [sub_mul, e1, ← hcg]
  simp only [smul_sub, smul_smul, sub_smul, one_smul]
  abel

theorem aux_pj_W_top {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (t : ℕ) :
    lemW A γ t t = -A⁻¹ := by
  simp [lemW, lemAlpha]

open scoped Matrix.Norms.L2Operator in
theorem aux_pj_matNorm_eq {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) : matNorm M = ‖M‖ := rfl

open scoped Matrix.Norms.L2Operator in
theorem aux_pj_G {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (hpos : ∀ t, 0 < γ t)
    (hinv : A⁻¹ * A = 1) (ε : ℝ) (hε : 0 < ε) (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hB : ∀ m, ‖(1 - ε • A) ^ m‖ ≤ C * q ^ m)
    (t j0 : ℕ) (g : ℕ → ℝ) (hgt : ‖A⁻¹‖ ≤ g t)
    (hrec : ∀ j, j0 ≤ j → j < t →
      γ j / γ (j + 1) * (|1 - γ (j + 1) / ε| + γ (j + 1) / ε * q) * g (j + 1)
        + |γ j / γ (j + 1) - 1| * ‖A⁻¹‖ ≤ g j) :
    ∀ n, n ≤ t - j0 → ∀ m, ‖lemW A γ (t - n) t * (1 - ε • A) ^ m‖ ≤ C * q ^ m * g (t - n) := by
  intro n
  induction n with
  | zero =>
    intro _ m
    simp only [Nat.sub_zero, aux_pj_W_top]
    have hCq : 0 ≤ C * q ^ m := mul_nonneg hC (pow_nonneg hq m)
    calc ‖-A⁻¹ * (1 - ε • A) ^ m‖ ≤ ‖A⁻¹‖ * ‖(1 - ε • A) ^ m‖ := by
          rw [neg_mul, norm_neg]; exact norm_mul_le _ _
      _ ≤ ‖A⁻¹‖ * (C * q ^ m) := mul_le_mul_of_nonneg_left (hB m) (norm_nonneg _)
      _ = C * q ^ m * ‖A⁻¹‖ := by ring
      _ ≤ C * q ^ m * g t := mul_le_mul_of_nonneg_left hgt hCq
  | succ n ih =>
    intro hn m
    have hj1 : t - n = t - (n + 1) + 1 := by omega
    have hjt : t - (n + 1) + 1 ≤ t := by omega
    set j := t - (n + 1) with hj
    have hγne := (hpos (j + 1)).ne'
    rw [aux_pj_W_rec A γ j t hjt hγne hinv]
    have ih0 := ih (by omega) m
    have ih1 := ih (by omega) (m + 1)
    rw [hj1] at ih0 ih1
    set c := γ j / γ (j + 1) with hc
    set p := γ (j + 1) / ε with hp
    set W := lemW A γ (j + 1) t with hW
    set B := 1 - ε • A with hBdef
    have hcpos : 0 < c := div_pos (hpos j) (hpos (j + 1))
    have hppos : 0 < p := div_pos (hpos (j + 1)) hε
    have hM : 1 - γ (j + 1) • A = (1 - p) • (1 : Matrix (Fin N) (Fin N) ℝ) + p • B := by
      have : p * ε = γ (j + 1) := by rw [hp, div_mul_cancel₀ _ hε.ne']
      rw [hBdef, smul_sub, smul_smul, this, sub_smul, one_smul]
      abel
    have hexp : (c • (W * (1 - γ (j + 1) • A)) + (c - 1) • A⁻¹) * B ^ m =
        (c * (1 - p)) • (W * B ^ m) + (c * p) • (W * B ^ (m + 1)) + (c - 1) • (A⁻¹ * B ^ m) := by
      rw [hM, pow_succ']
      simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, mul_assoc]
      rw [smul_add, smul_smul, smul_smul]
    rw [hexp]
    have hCq : 0 ≤ C * q ^ m := mul_nonneg hC (pow_nonneg hq m)
    have hY : ‖A⁻¹ * B ^ m‖ ≤ ‖A⁻¹‖ * (C * q ^ m) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hB m) (norm_nonneg _))
    have key := hrec j (by omega) (by omega)
    calc ‖(c * (1 - p)) • (W * B ^ m) + (c * p) • (W * B ^ (m + 1)) + (c - 1) • (A⁻¹ * B ^ m)‖
        ≤ ‖(c * (1 - p)) • (W * B ^ m)‖ + ‖(c * p) • (W * B ^ (m + 1))‖
            + ‖(c - 1) • (A⁻¹ * B ^ m)‖ := norm_add₃_le
      _ = c * |1 - p| * ‖W * B ^ m‖ + c * p * ‖W * B ^ (m + 1)‖ + |c - 1| * ‖A⁻¹ * B ^ m‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_mul, abs_of_pos hcpos, abs_mul, abs_of_pos hcpos,
            abs_of_pos hppos]
      _ ≤ c * |1 - p| * (C * q ^ m * g (j + 1)) + c * p * (C * q ^ (m + 1) * g (j + 1))
            + |c - 1| * (‖A⁻¹‖ * (C * q ^ m)) := by
          gcongr
      _ = C * q ^ m * (c * (|1 - p| + p * q) * g (j + 1) + |c - 1| * ‖A⁻¹‖) := by ring
      _ ≤ C * q ^ m * g j := mul_le_mul_of_nonneg_left key hCq

theorem aux_pj_step_lim (γ : ℕ → ℝ) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ) :
    Tendsto (fun j => (γ j - γ (j + 1)) / γ (j + 1) ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun j => 1 / γ (j + 1) - 1 / γ j) atTop (𝓝 0) := by
  obtain ⟨_, h0, ho⟩ := hγ
  have hr : Tendsto (fun t => (γ t - γ (t + 1)) / γ t / γ t) atTop (𝓝 0) :=
    ho.tendsto_div_nhds_zero
  have hr2 : Tendsto (fun t => (γ t - γ (t + 1)) / γ t) atTop (𝓝 0) := by
    have := hr.mul h0
    simp only [zero_mul] at this
    refine this.congr (fun t => ?_)
    have := (hpos t).ne'
    field_simp
  have hratio : Tendsto (fun t => γ t / γ (t + 1)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t => γ (t + 1) / γ t) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub hr2
      simp only [sub_zero] at this
      refine this.congr (fun t => ?_)
      have := (hpos t).ne'
      field_simp
      ring
    have := h1.inv₀ one_ne_zero
    simp only [inv_one] at this
    refine this.congr (fun t => ?_)
    rw [inv_div]
  constructor
  · have := hr.mul (hratio.pow 2)
    simp only [zero_mul] at this
    refine this.congr (fun t => ?_)
    have := (hpos t).ne'
    have := (hpos (t + 1)).ne'
    field_simp
  · have := hr.mul hratio
    simp only [zero_mul] at this
    refine this.congr (fun t => ?_)
    have := (hpos t).ne'
    have := (hpos (t + 1)).ne'
    field_simp

theorem aux_pj_u_bound (γ : ℕ → ℝ) (hpos : ∀ t, 0 < γ t)
    (hu : Tendsto (fun j => 1 / γ (j + 1) - 1 / γ j) atTop (𝓝 0)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M, ∀ j : ℕ, 1 / γ j ≤ M + δ * j := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hu.eventually (gt_mem_nhds hδ))
  have hnn : ∀ i, 0 ≤ 1 / γ i := fun i => (one_div_pos.2 (hpos i)).le
  refine ⟨∑ i ∈ Finset.range (J + 1), 1 / γ i, fun j => ?_⟩
  have hJle : 1 / γ J ≤ ∑ i ∈ Finset.range (J + 1), 1 / γ i :=
    Finset.single_le_sum (fun i _ => hnn i) (Finset.self_mem_range_succ J)
  rcases le_or_gt j J with h | h
  · have h1 : 1 / γ j ≤ ∑ i ∈ Finset.range (J + 1), 1 / γ i :=
      Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_range.2 (by omega))
    have : 0 ≤ δ * j := by positivity
    linarith
  · have key : ∀ k : ℕ, 1 / γ (J + k) ≤ 1 / γ J + δ * k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have := hJ (J + k) (by omega)
        rw [← add_assoc]
        push_cast
        linarith
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    have h2 := key k
    have h3 : δ * (k : ℝ) ≤ δ * ((J + k : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      push_cast
      have : (0 : ℝ) ≤ J := by positivity
      linarith
    linarith

theorem aux_pj_K1 (γj g ε q a δ x : ℝ) (hg : 0 < g) (hε : 0 < ε) (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hgε : g ≤ ε) (hx : 0 ≤ x)
    (hs1 : |(γj - g) / g ^ 2| ≤ (1 - q) / ε / 2)
    (hs2 : |(γj - g) / g ^ 2| * (a + 1) ≤ (1 - q) / ε / 2 * δ) :
    γj / g * (|1 - g / ε| + g / ε * q) * x + |γj / g - 1| * a ≤
      (1 - (1 - q) / ε / 2 * g) * x + (1 - q) / ε / 2 * δ * g ∧
    0 ≤ 1 - (1 - q) / ε / 2 * g := by
  set s := (γj - g) / g ^ 2 with hs
  set L := (1 - q) / ε with hL
  have hc : γj / g = 1 + s * g := by rw [hs]; field_simp; ring
  have hpg : g / ε ≤ 1 := (div_le_one hε).2 hgε
  have hpg0 : 0 ≤ g / ε := (div_pos hg hε).le
  have habs : |1 - g / ε| = 1 - g / ε := abs_of_nonneg (by linarith)
  have hLg : L * g = (1 - q) * (g / ε) := by rw [hL]; ring
  have hρ : |1 - g / ε| + g / ε * q = 1 - L * g := by rw [habs, hLg]; ring
  have hLg1 : L * g ≤ 1 - q := by rw [hLg]; nlinarith
  have hLg0 : 0 ≤ L * g := by rw [hLg]; nlinarith
  have hsg : s * g ≤ |s| * g := mul_le_mul_of_nonneg_right (le_abs_self s) hg.le
  have hsabs0 : 0 ≤ |s| := abs_nonneg s
  have hcρ : (1 + s * g) * (1 - L * g) ≤ 1 - L / 2 * g := by
    have e1 : s * g * (1 - L * g) ≤ |s| * g * (1 - L * g) :=
      mul_le_mul_of_nonneg_right hsg (by linarith)
    have e2 : |s| * g * (1 - L * g) ≤ |s| * g := by
      have : 0 ≤ |s| * g * (L * g) := by positivity
      nlinarith
    have e3 : |s| * g ≤ L / 2 * g := mul_le_mul_of_nonneg_right hs1 hg.le
    nlinarith
  have hc1 : |γj / g - 1| = |s| * g := by rw [hc, add_sub_cancel_left, abs_mul, abs_of_pos hg]
  refine ⟨?_, by nlinarith⟩
  rw [hc1, hc, hρ]
  have t1 : (1 + s * g) * (1 - L * g) * x ≤ (1 - L / 2 * g) * x :=
    mul_le_mul_of_nonneg_right hcρ hx
  have t2 : |s| * g * a ≤ L / 2 * δ * g := by
    have : |s| * g * a ≤ |s| * (a + 1) * g := by nlinarith
    have : |s| * (a + 1) * g ≤ L / 2 * δ * g := mul_le_mul_of_nonneg_right hs2 hg.le
    linarith
  linarith

theorem aux_pj_tele (γ : ℕ → ℝ) (hpos : ∀ t, 0 < γ t) (L : ℝ) (hL : 0 < L) (J t : ℕ) (hJt : J ≤ t)
    (hfac : ∀ k, J < k → 0 ≤ 1 - L * γ k) (U : ℝ) (hU0 : 0 ≤ U)
    (hU : ∀ j, j < t → 1 / γ (j + 1) ≤ U) :
    ∑ j ∈ Finset.Ico J t, ∏ k ∈ Finset.Ico (j + 1) (t + 1), (1 - L * γ k) ≤ U / L := by
  set P : ℕ → ℝ := fun j => ∏ k ∈ Finset.Ico (j + 1) (t + 1), (1 - L * γ k) with hP
  have hPnn : ∀ j, J ≤ j → 0 ≤ P j := fun j hj =>
    Finset.prod_nonneg (fun k hk => hfac k (by rw [Finset.mem_Ico] at hk; omega))
  have hPrec : ∀ j, j < t → P j = (1 - L * γ (j + 1)) * P (j + 1) := fun j hj => by
    simp only [hP]
    rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : j + 1 < t + 1)]
  have hPt : P t = 1 := by simp [hP]
  have hterm : ∀ j ∈ Finset.Ico J t, P j ≤ U / L * (P (j + 1) - P j) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hr := hPrec j hj.2
    have hn := hPnn (j + 1) (by omega)
    have hg := hpos (j + 1)
    have hdiff : P (j + 1) - P j = L * γ (j + 1) * P (j + 1) := by rw [hr]; ring
    have hle : P j ≤ P (j + 1) := by
      rw [hr]; have : 0 ≤ L * γ (j + 1) * P (j + 1) := by positivity
      nlinarith
    have hUj := hU j hj.2
    have : P (j + 1) ≤ U / L * (P (j + 1) - P j) := by
      rw [hdiff]
      have e : U / L * (L * γ (j + 1) * P (j + 1)) = U * γ (j + 1) * P (j + 1) := by
        field_simp
      rw [e]
      have h1 : 1 ≤ U * γ (j + 1) := by
        rw [div_le_iff₀ hg] at hUj; linarith
      nlinarith
    linarith
  calc ∑ j ∈ Finset.Ico J t, P j ≤ ∑ j ∈ Finset.Ico J t, U / L * (P (j + 1) - P j) :=
        Finset.sum_le_sum hterm
    _ = U / L * (P t - P J) := by rw [← Finset.mul_sum, Finset.sum_Ico_sub P hJt]
    _ ≤ U / L := by
        rw [hPt]
        have := hPnn J le_rfl
        have : 0 ≤ U / L := div_nonneg hU0 hL.le
        nlinarith

theorem aux_pj_matApply_eq {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    matApply M v = Matrix.toEuclideanCLM (𝕜 := ℝ) M v := rfl

theorem aux_pj_iter {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ)
    (Δ₀ : EuclideanSpace ℝ (Fin N)) (ξ : ℕ → EuclideanSpace ℝ (Fin N)) (i : ℕ) :
    detIterate Δ₀ γ (matApply A) ξ i =
      matApply (lemX A γ 1 (i + 1)) Δ₀ -
        ∑ j ∈ Finset.Ico 1 (i + 1), γ j • matApply (lemX A γ (j + 1) (i + 1)) (ξ j) := by
  induction i with
  | zero => simp [detIterate, aux_pj_X_self, matApply]
  | succ i ih =>
    rw [detIterate, ih]
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ i + 1), aux_pj_X_self]
    rw [aux_pj_X_succ A γ 1 (i + 1) (by omega)]
    have hs : ∀ j ∈ Finset.Ico 1 (i + 1), lemX A γ (j + 1) (i + 1 + 1) =
        (1 - γ (i + 1) • A) * lemX A γ (j + 1) (i + 1) := fun j hj =>
      aux_pj_X_succ A γ (j + 1) (i + 1) (by rw [Finset.mem_Ico] at hj; omega)
    set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N)
    set g := γ (i + 1)
    set L := T (1 - g • A)
    have key : ∀ M v, T ((1 - g • A) * M) v = L (T M v) := by
      intro M v; rw [map_mul]; rfl
    have key2 : ∀ w, L w = w - g • T A w := by
      intro w; simp [L, map_sub, map_smul]
    have hsum : ∑ k ∈ Finset.Ico 1 (i + 1), γ k • matApply (lemX A γ (k + 1) (i + 1 + 1)) (ξ k) =
        L (∑ k ∈ Finset.Ico 1 (i + 1), γ k • matApply (lemX A γ (k + 1) (i + 1)) (ξ k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [hs k hk, map_smul, aux_pj_matApply_eq, aux_pj_matApply_eq, key]
    rw [hsum, aux_pj_matApply_eq ((1 - g • A) * _), aux_pj_matApply_eq 1, key, map_one,
      one_apply_eq_self]
    set y := matApply (lemX A γ 1 (i + 1)) Δ₀ -
      ∑ k ∈ Finset.Ico 1 (i + 1), γ k • matApply (lemX A γ (k + 1) (i + 1)) (ξ k) with hy
    have hy2 : L (T (lemX A γ 1 (i + 1)) Δ₀) -
        L (∑ k ∈ Finset.Ico 1 (i + 1), γ k • matApply (lemX A γ (k + 1) (i + 1)) (ξ k)) = L y := by
      rw [hy, map_sub]; rfl
    rw [sub_add_eq_sub_sub, hy2, key2, aux_pj_matApply_eq A, smul_add]
    abel

theorem aux_pj_sum_iter {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (hγ0 : γ 0 ≠ 0)
    (Δ₀ : EuclideanSpace ℝ (Fin N)) (ξ : ℕ → EuclideanSpace ℝ (Fin N)) (t : ℕ) :
    ∑ i ∈ Finset.range t, detIterate Δ₀ γ (matApply A) ξ i =
      (γ 0)⁻¹ • matApply (lemAlpha A γ 0 t) Δ₀ -
        ∑ j ∈ Finset.Ico 1 t, matApply (lemAlpha A γ j t) (ξ j) := by
  simp only [aux_pj_iter, Finset.sum_sub_distrib]
  congr 1
  · simp only [lemAlpha, aux_pj_matApply_eq, map_smul, ContinuousLinearMap.smul_apply, smul_smul,
      inv_mul_cancel₀ hγ0, one_smul, map_sum, ContinuousLinearMap.sum_apply, Finset.range_eq_Ico]
  · rw [Finset.sum_comm' (t' := Finset.Ico 1 t) (s' := fun j => Finset.Ico j t)]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [lemAlpha, aux_pj_matApply_eq, map_smul, ContinuousLinearMap.smul_apply,
        map_sum, ContinuousLinearMap.sum_apply, Finset.smul_sum]
    · intro x y
      simp only [Finset.mem_range, Finset.mem_Ico]
      omega

theorem aux_pj_part1 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (hγ0 : γ 0 ≠ 0)
    (Δ₀ : EuclideanSpace ℝ (Fin N)) (ξ : ℕ → EuclideanSpace ℝ (Fin N)) :
    ∀ t : ℕ, 1 ≤ t →
      Real.sqrt t • detAverage Δ₀ γ (matApply A) ξ t =
        (Real.sqrt t * γ 0)⁻¹ • matApply (lemAlpha A γ 0 t) Δ₀
          - (Real.sqrt t)⁻¹ • ∑ j ∈ Finset.Ico 1 t, matApply A⁻¹ (ξ j)
          - (Real.sqrt t)⁻¹ • ∑ j ∈ Finset.Ico 1 t, matApply (lemW A γ j t) (ξ j) := by
  intro t ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hsq : Real.sqrt t * (t : ℝ)⁻¹ = (Real.sqrt t)⁻¹ := by
    have h1 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt htpos.le
    have h2 : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
    rw [mul_inv_eq_iff_eq_mul₀ htpos.ne', eq_comm, inv_mul_eq_iff_eq_mul₀ h2.ne', h1]
  have hα : ∀ j, matApply (lemAlpha A γ j t) (ξ j) =
      matApply A⁻¹ (ξ j) + matApply (lemW A γ j t) (ξ j) := by
    intro j
    simp only [lemW, aux_pj_matApply_eq, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [detAverage, aux_pj_sum_iter A γ hγ0, smul_smul, hsq]
  simp only [hα, Finset.sum_add_distrib, smul_sub, smul_add, smul_smul, mul_inv]
  abel

open scoped Matrix.Norms.L2Operator in
theorem aux_pj_normone {N : ℕ} : ‖(1 : Matrix (Fin N) (Fin N) ℝ)‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le

open scoped Matrix.Norms.L2Operator in
theorem aux_pj_C {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → ‖B ^ n‖ ≤ q ^ n) : ∃ C, 0 ≤ C ∧ ∀ n, ‖B ^ n‖ ≤ C * q ^ n := by
  set X := max 1 ‖B‖ with hX
  have hX1 : 1 ≤ X := le_max_left _ _
  have hpowX : ∀ n, ‖B ^ n‖ ≤ X ^ n := by
    intro n
    induction n with
    | zero => simpa using aux_pj_normone
    | succ n ih =>
      rw [pow_succ, pow_succ]
      calc ‖B ^ n * B‖ ≤ ‖B ^ n‖ * ‖B‖ := norm_mul_le _ _
        _ ≤ X ^ n * X := mul_le_mul ih (le_max_right _ _) (norm_nonneg _) (by positivity)
  refine ⟨X ^ n₀ / q ^ n₀, by positivity, fun n => ?_⟩
  have hC1 : 1 ≤ X ^ n₀ / q ^ n₀ := by
    rw [one_le_div (by positivity)]
    calc q ^ n₀ ≤ 1 := pow_le_one₀ hq0.le hq1.le
      _ ≤ X ^ n₀ := one_le_pow₀ hX1
  rcases le_or_gt n₀ n with hn | hn
  · calc ‖B ^ n‖ ≤ q ^ n := h n hn
      _ = 1 * q ^ n := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hC1 (by positivity)
  · calc ‖B ^ n‖ ≤ X ^ n := hpowX n
      _ ≤ X ^ n₀ := pow_le_pow_right₀ hX1 hn.le
      _ = X ^ n₀ / q ^ n₀ * q ^ n₀ := by field_simp
      _ ≤ X ^ n₀ / q ^ n₀ * q ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0.le hq1.le hn.le) (by positivity)

theorem aux_pj_tendsto_crit (f : ℕ → ℝ) (hf : ∀ t, 0 ≤ f t)
    (h : ∀ δ > 0, ∃ X : ℝ, ∃ T : ℕ, ∀ t, T ≤ t → f t ≤ X / t + δ) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨X, T, hT⟩ := h (η / 2) (by positivity)
  obtain ⟨T0, hT0⟩ := exists_nat_gt (2 * |X| / η)
  refine ⟨max T (T0 + 1), fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf t)]
  have h1 := hT t (le_of_max_le_left ht)
  have ht2 : ((T0 + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast le_of_max_le_right ht
  push_cast at ht2
  have hT0nn : (0 : ℝ) ≤ T0 := by positivity
  have tpos : 0 < (t : ℝ) := by linarith
  have hX : X / t < η / 2 := by
    rw [div_lt_iff₀ tpos]
    have h3 : 2 * |X| / η < t := by linarith
    rw [div_lt_iff₀ hη] at h3
    have := le_abs_self X
    nlinarith
  linarith

open scoped Matrix.Norms.L2Operator in
theorem aux_pj_part2 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ)
    (hA : EigenRePos A) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ) :
    ∃ K : ℝ, (∀ t, matNorm (lemAlpha A γ 0 t) ≤ K) ∧
      (∀ j t, 1 ≤ j → j < t → matNorm (lemW A γ j t) ≤ K) ∧
      Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * ∑ j ∈ Finset.Ico 1 t, matNorm (lemW A γ j t))
        atTop (𝓝 0) := by
  have hinv : A⁻¹ * A = 1 := by
    apply Matrix.nonsing_inv_mul
    have h0 : (0 : ℂ) ∉ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := fun h => by
      have := hA 0 h; simp at this
    rw [spectrum.zero_mem_iff, not_not, Matrix.isUnit_iff_isUnit_det] at h0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h0
    apply Ne.isUnit
    intro hd
    rw [hd, map_zero] at h0
    exact not_isUnit_zero h0
  obtain ⟨ε, hε, q, hq0, hq1, n₀, hn₀⟩ := aux_pj_spec A hA
  obtain ⟨C, hC, hB⟩ := aux_pj_C (1 - ε • A) q hq0 hq1 n₀ (fun n hn => hn₀ n hn)
  obtain ⟨hs, hu⟩ := aux_pj_step_lim γ hpos hγ
  set a := ‖A⁻¹‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  set L := (1 - q) / ε / 2 with hL
  have hLpos : 0 < L := by
    have h1 : 0 < 1 - q := by linarith
    rw [hL]; positivity
  have hgood : ∀ δ > 0, ∃ J : ℕ, ∀ j, J ≤ j → γ (j + 1) ≤ ε ∧
      |(γ j - γ (j + 1)) / γ (j + 1) ^ 2| ≤ L ∧
      |(γ j - γ (j + 1)) / γ (j + 1) ^ 2| * (a + 1) ≤ L * δ := by
    intro δ hδ
    have e1 : ∀ᶠ j in atTop, γ (j + 1) ≤ ε := by
      have := (tendsto_add_atTop_iff_nat 1).2 hγ.2.1
      exact this.eventually (ge_mem_nhds hε)
    set κ := min L (L * δ / (a + 1)) with hκdef
    have hκ : 0 < κ := lt_min hLpos (by positivity)
    have e2 : ∀ᶠ j in atTop, |(γ j - γ (j + 1)) / γ (j + 1) ^ 2| < κ := by
      have := hs.eventually (Metric.ball_mem_nhds 0 hκ)
      filter_upwards [this] with j hj
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hj
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (e1.and e2)
    refine ⟨J, fun j hj => ⟨(hJ j hj).1, ?_, ?_⟩⟩
    · exact ((hJ j hj).2.trans_le (min_le_left _ _)).le
    · have h2 := (hJ j hj).2
      have : κ ≤ L * δ / (a + 1) := min_le_right _ _
      calc _ ≤ κ * (a + 1) := mul_le_mul_of_nonneg_right h2.le (by positivity)
        _ ≤ L * δ / (a + 1) * (a + 1) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = L * δ := by field_simp
  have hstep : ∀ δ > 0, ∀ J : ℕ, (∀ j, J ≤ j → γ (j + 1) ≤ ε ∧
      |(γ j - γ (j + 1)) / γ (j + 1) ^ 2| ≤ L ∧
      |(γ j - γ (j + 1)) / γ (j + 1) ^ 2| * (a + 1) ≤ L * δ) → ∀ j, J ≤ j → ∀ x, 0 ≤ x →
      γ j / γ (j + 1) * (|1 - γ (j + 1) / ε| + γ (j + 1) / ε * q) * x
        + |γ j / γ (j + 1) - 1| * a ≤ (1 - L * γ (j + 1)) * x + L * δ * γ (j + 1) ∧
      0 ≤ 1 - L * γ (j + 1) := by
    intro δ _ J hJ j hj x hx
    obtain ⟨g1, g2, g3⟩ := hJ j hj
    exact aux_pj_K1 (γ j) (γ (j + 1)) ε q a δ x (hpos (j + 1)) hε hq0.le hq1 g1 hx g2 g3
  -- uniform bound
  obtain ⟨J1, hJ1⟩ := hgood 1 one_pos
  set f : ℕ → ℝ := fun k => γ k / γ (k + 1) * (|1 - γ (k + 1) / ε| + γ (k + 1) / ε * q)
    + |γ k / γ (k + 1) - 1| with hfdef
  have hf0 : ∀ k, 0 ≤ f k := by
    intro k
    have h1 : 0 < γ k / γ (k + 1) := div_pos (hpos k) (hpos (k + 1))
    have h2 : 0 ≤ γ (k + 1) / ε * q := mul_nonneg (div_pos (hpos (k + 1)) hε).le hq0.le
    simp only [hfdef]
    positivity
  set F := 1 + ∑ k ∈ Finset.range J1, f k with hF
  have hF1 : 1 ≤ F := by
    have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.range J1) => hf0 k)
    linarith
  have hfF : ∀ k, k < J1 → f k ≤ F := by
    intro k hk
    have := Finset.single_le_sum (fun i (_ : i ∈ Finset.range J1) => hf0 i)
      (Finset.mem_range.2 hk)
    linarith
  set R : ℕ → ℝ := fun j => (a + 1) * F ^ (J1 - j) with hR
  have hRa : ∀ j, a + 1 ≤ R j := by
    intro j
    have : 1 ≤ F ^ (J1 - j) := one_le_pow₀ hF1
    simp only [hR]
    nlinarith
  have hRmax : ∀ j, R j ≤ (a + 1) * F ^ J1 := by
    intro j
    simp only [hR]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hF1 (Nat.sub_le _ _)) (by positivity)
  have hRrec : ∀ j, γ j / γ (j + 1) * (|1 - γ (j + 1) / ε| + γ (j + 1) / ε * q) * R (j + 1)
      + |γ j / γ (j + 1) - 1| * a ≤ R j := by
    intro j
    by_cases hj : J1 ≤ j
    · have e1 : R j = a + 1 := by simp [hR, Nat.sub_eq_zero_of_le hj]
      have e2 : R (j + 1) = a + 1 := by simp [hR, Nat.sub_eq_zero_of_le (by omega : J1 ≤ j + 1)]
      rw [e1, e2]
      obtain ⟨k1, k2⟩ := hstep 1 one_pos J1 hJ1 j hj (a + 1) (by positivity)
      have : 0 ≤ L * γ (j + 1) * a := by have := hpos (j + 1); positivity
      nlinarith
    · rw [not_le] at hj
      have e1 : R j = f j * R (j + 1) + (F - f j) * R (j + 1) := by
        simp only [hR]
        rw [show J1 - j = (J1 - (j + 1)) + 1 by omega, pow_succ]
        ring
      have hRj1 := hRa (j + 1)
      have hR0 : 0 ≤ R (j + 1) := by linarith
      have hFf : 0 ≤ (F - f j) * R (j + 1) := mul_nonneg (by linarith [hfF j hj]) hR0
      rw [e1]
      simp only [hfdef]
      have : |γ j / γ (j + 1) - 1| * a ≤ |γ j / γ (j + 1) - 1| * R (j + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      nlinarith
  set K0 := C * ((a + 1) * F ^ J1) with hK0
  have hWbd : ∀ j t, j ≤ t → ‖lemW A γ j t‖ ≤ K0 := by
    intro j t hjt
    have hG := aux_pj_G A γ hpos hinv ε hε C q hC hq0.le hB t 0 R (by linarith [hRa t])
      (fun j _ _ => hRrec j) (t - j) (by omega) 0
    rw [Nat.sub_sub_self hjt, pow_zero, mul_one, pow_zero, mul_one] at hG
    exact hG.trans (mul_le_mul_of_nonneg_left (hRmax j) hC)
  have hK0nn : 0 ≤ K0 := le_trans (norm_nonneg _) (hWbd 0 0 le_rfl)
  refine ⟨K0 + a, fun t => ?_, fun j t _ hjt => ?_, ?_⟩
  · rw [aux_pj_matNorm_eq]
    have : lemAlpha A γ 0 t = lemW A γ 0 t + A⁻¹ := by simp [lemW]
    rw [this]
    exact (norm_add_le _ _).trans (by linarith [hWbd 0 t (Nat.zero_le _)])
  · rw [aux_pj_matNorm_eq]
    linarith [hWbd j t hjt.le]
  · apply aux_pj_tendsto_crit
    · intro t
      exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
        (Finset.sum_nonneg (fun j _ => norm_nonneg _))
    intro δ' hδ'
    set D := C + C * a / L with hD
    have hD0 : 0 ≤ D := by positivity
    set δ := δ' / (D + 1) with hδdef
    have hδ : 0 < δ := by positivity
    have hδD : δ * D ≤ δ' := by
      rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    obtain ⟨J, hJ⟩ := hgood δ hδ
    obtain ⟨Mu, hMu⟩ := aux_pj_u_bound γ hpos hu δ hδ
    refine ⟨J * K0 + C * a * |Mu| / L, J + 1, fun t ht => ?_⟩
    have hJt : J ≤ t := by omega
    have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hfac : ∀ k, J < k → 0 ≤ 1 - L * γ k := by
      intro k hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact (hstep δ hδ J hJ k' (by omega) 0 le_rfl).2
    set P : ℕ → ℝ := fun j => ∏ k ∈ Finset.Ico (j + 1) (t + 1), (1 - L * γ k) with hP
    have hPnn : ∀ j, J ≤ j → 0 ≤ P j := fun j hj =>
      Finset.prod_nonneg (fun k hk => hfac k (by rw [Finset.mem_Ico] at hk; omega))
    have hPrec : ∀ j, j < t → P j = (1 - L * γ (j + 1)) * P (j + 1) := fun j hj => by
      simp only [hP]
      rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : j + 1 < t + 1)]
    have hPt : P t = 1 := by simp [hP]
    have hWavg : ∀ j, J ≤ j → j ≤ t → ‖lemW A γ j t‖ ≤ C * (δ + a * P j) := by
      intro j hj hjt
      have hG := aux_pj_G A γ hpos hinv ε hε C q hC hq0.le hB t J (fun j => δ + a * P j)
        (by simp only [hPt]; linarith)
        (fun i hi hit => by
          have hPi := hPnn (i + 1) (by omega)
          obtain ⟨k1, k2⟩ := hstep δ hδ J hJ i hi (δ + a * P (i + 1)) (by positivity)
          rw [hPrec i hit]
          nlinarith [k1])
        (t - j) (by omega) 0
      rw [Nat.sub_sub_self hjt, pow_zero, mul_one, pow_zero, mul_one] at hG
      exact hG
    have hsumP : ∑ j ∈ Finset.Ico J t, P j ≤ (|Mu| + δ * t) / L :=
      aux_pj_tele γ hpos L hLpos J t hJt hfac (|Mu| + δ * t) (by positivity)
        (fun j hj => by
          have h1 := hMu (j + 1)
          have h2 : ((j + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast hj
          have h3 := mul_le_mul_of_nonneg_left h2 hδ.le
          have h4 := le_abs_self Mu
          linarith)
    have hsplit : ∑ j ∈ Finset.Ico 1 t, matNorm (lemW A γ j t) ≤
        ∑ j ∈ Finset.range t, ‖lemW A γ j t‖ := by
      simp only [aux_pj_matNorm_eq]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
        omega
      · intro j _ _
        exact norm_nonneg _
    rw [← Finset.sum_range_add_sum_Ico _ hJt] at hsplit
    have h1 : ∑ j ∈ Finset.range J, ‖lemW A γ j t‖ ≤ J * K0 := by
      calc ∑ j ∈ Finset.range J, ‖lemW A γ j t‖ ≤ ∑ j ∈ Finset.range J, K0 :=
            Finset.sum_le_sum (fun j hj => hWbd j t (by rw [Finset.mem_range] at hj; omega))
        _ = J * K0 := by simp
    have h2 : ∑ j ∈ Finset.Ico J t, ‖lemW A γ j t‖ ≤
        ∑ j ∈ Finset.Ico J t, (C * δ + C * a * P j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_Ico] at hj
      calc ‖lemW A γ j t‖ ≤ C * (δ + a * P j) := hWavg j hj.1 hj.2.le
        _ = C * δ + C * a * P j := by ring
    have h2' : ∑ j ∈ Finset.Ico J t, ‖lemW A γ j t‖ ≤
        ∑ j ∈ Finset.Ico J t, C * δ + C * a * ∑ j ∈ Finset.Ico J t, P j := by
      refine h2.trans (le_of_eq ?_)
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    have h3 : ∑ j ∈ Finset.Ico J t, C * δ ≤ t * (C * δ) := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have : ((t - J : ℕ) : ℝ) ≤ t := by exact_mod_cast Nat.sub_le t J
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h4 : C * a * ∑ j ∈ Finset.Ico J t, P j ≤ C * a * ((|Mu| + δ * t) / L) :=
      mul_le_mul_of_nonneg_left hsumP (by positivity)
    have htot : ∑ j ∈ Finset.Ico 1 t, matNorm (lemW A γ j t) ≤
        J * K0 + t * (C * δ) + C * a * ((|Mu| + δ * t) / L) := by linarith
    calc (t : ℝ)⁻¹ * ∑ j ∈ Finset.Ico 1 t, matNorm (lemW A γ j t)
        ≤ (t : ℝ)⁻¹ * (J * K0 + t * (C * δ) + C * a * ((|Mu| + δ * t) / L)) :=
          mul_le_mul_of_nonneg_left htot (inv_nonneg.2 htpos.le)
      _ = (J * K0 + C * a * |Mu| / L) / t + δ * D := by
          rw [hD]; field_simp; ring
      _ ≤ (J * K0 + C * a * |Mu| / L) / t + δ' := by linarith

end PolyakJuditsky.Averaging
open PolyakJuditsky.Averaging
open Filter Topology

theorem solution {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ)
    (hA : EigenRePos A) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ)
    (Δ₀ : EuclideanSpace ℝ (Fin N)) (ξ : ℕ → EuclideanSpace ℝ (Fin N)) :
    (∀ t : ℕ, 1 ≤ t →
      Real.sqrt t • detAverage Δ₀ γ (matApply A) ξ t =
        (Real.sqrt t * γ 0)⁻¹ • matApply (lemAlpha A γ 0 t) Δ₀
          - (Real.sqrt t)⁻¹ • ∑ j ∈ Finset.Ico 1 t, matApply A⁻¹ (ξ j)
          - (Real.sqrt t)⁻¹ • ∑ j ∈ Finset.Ico 1 t, matApply (lemW A γ j t) (ξ j)) ∧
    ∃ K : ℝ, (∀ t, matNorm (lemAlpha A γ 0 t) ≤ K) ∧
      (∀ j t, 1 ≤ j → j < t → matNorm (lemW A γ j t) ≤ K) ∧
      Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * ∑ j ∈ Finset.Ico 1 t, matNorm (lemW A γ j t))
        atTop (𝓝 0) :=
  ⟨aux_pj_part1 A γ (hpos 0).ne' Δ₀ ξ, aux_pj_part2 A γ hA hpos hγ⟩
