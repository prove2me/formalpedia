-- Prove2me | solution 1 for PolyakJuditsky.Averaging.lemma1_phi_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:40:16.207159+00:00
-- url     : https://prove2.me/submissions/5f4bd4f8-48a6-4238-8359-0894cd6e8db0

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open Filter Topology

namespace PolyakJuditsky.Averaging

open scoped Matrix.Norms.Operator in
lemma aux_pj_matNorm_le_linfty (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : Matrix (Fin N) (Fin N) ℝ, matNorm M ≤ C * ‖M‖ := by
  refine ⟨∑ i : Fin N, ∑ j : Fin N,
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.single i j (1:ℝ))‖, by positivity, fun M => ?_⟩
  have hentry : ∀ i j, ‖M i j‖ ≤ ‖M‖ := by
    intro i j
    rw [Matrix.linfty_opNorm_def]
    have h1 : ‖M i j‖₊ ≤ ∑ k, ‖M i k‖₊ :=
      Finset.single_le_sum (f := fun k => ‖M i k‖₊) (fun k _ => zero_le) (Finset.mem_univ j)
    have h2 : ∑ k, ‖M i k‖₊ ≤ Finset.univ.sup fun i => ∑ k, ‖M i k‖₊ :=
      Finset.le_sup (f := fun i => ∑ k, ‖M i k‖₊) (Finset.mem_univ i)
    have := h1.trans h2
    rw [← coe_nnnorm]; exact_mod_cast this
  unfold matNorm
  have e : Matrix.toEuclideanCLM (𝕜 := ℝ) M = ∑ i : Fin N, ∑ j : Fin N,
      M i j • Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.single i j (1:ℝ)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [map_sum, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hentry i j) (norm_nonneg _)

open scoped Matrix.Norms.Operator in
lemma aux_pj_spec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : EigenRePos A) :
    ∃ h : ℝ, 0 < h ∧ ∃ L : ℕ, 1 ≤ L ∧ matNorm ((1 - h • A) ^ L) ≤ 1/2 := by
  set Aℂ := A.map (algebraMap ℝ ℂ) with hAℂ
  obtain ⟨m, M, hm, hmM, hbd⟩ : ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ μ ∈ spectrum ℂ Aℂ, m ≤ μ.re ∧ ‖μ‖ ≤ M := by
    by_cases hne : (spectrum ℂ Aℂ).Nonempty
    · obtain ⟨μ0, hμ0, hmin⟩ :=
        (spectrum.isCompact Aℂ).exists_isMinOn hne Complex.continuous_re.continuousOn
      obtain ⟨μ1, hμ1, hmax⟩ :=
        (spectrum.isCompact Aℂ).exists_isMaxOn hne continuous_norm.continuousOn
      refine ⟨μ0.re, ‖μ1‖, hA μ0 hμ0, ?_, fun μ hμ => ⟨hmin hμ, hmax hμ⟩⟩
      exact (Complex.re_le_norm μ0).trans (hmax hμ0)
    · exact ⟨1, 1, one_pos, le_rfl, fun μ hμ => absurd ⟨μ, hμ⟩ hne⟩
  have hMpos : 0 < M := lt_of_lt_of_le hm hmM
  set h : ℝ := m / M ^ 2 with hhdef
  have hh : 0 < h := by positivity
  set B : Matrix (Fin N) (Fin N) ℝ := 1 - h • A with hB
  set Bℂ := B.map (algebraMap ℝ ℂ) with hBℂ
  have hBℂ' : Bℂ = 1 - (h : ℂ) • Aℂ := by
    ext i j
    simp [hBℂ, hB, hAℂ, Matrix.one_apply]
    split_ifs <;> simp
  set q : ℝ := (1 + (1 - m ^ 2 / M ^ 2)) / 2 with hqdef
  have hmM2 : m ^ 2 / M ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hq0 : 0 ≤ q := by rw [hqdef]; linarith
  have hmM3 : 0 < m ^ 2 / M ^ 2 := by positivity
  have hq1 : q < 1 := by rw [hqdef]; linarith
  have hspec : ∀ z ∈ spectrum ℂ Bℂ, ‖z‖ ≤ q := by
    intro z hz
    set μ : ℂ := (1 - z) / (h : ℂ) with hμdef
    have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have hzμ : z = 1 - (h : ℂ) * μ := by rw [hμdef]; field_simp; ring
    have hμ : μ ∈ spectrum ℂ Aℂ := by
      rw [spectrum.mem_iff] at hz ⊢
      intro hu; apply hz
      have : algebraMap ℂ _ z - Bℂ = algebraMap ℂ _ (-(h : ℂ)) * (algebraMap ℂ _ μ - Aℂ) := by
        rw [← Algebra.smul_def, hBℂ', hzμ, Algebra.algebraMap_eq_smul_one,
          Algebra.algebraMap_eq_smul_one]
        module
      rw [this]
      exact (IsUnit.map _ (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hhc))).mul hu
    obtain ⟨h1, h2⟩ := hbd μ hμ
    have hsq : ‖z‖ ^ 2 ≤ 1 - m ^ 2 / M ^ 2 := by
      rw [hzμ, Complex.sq_norm, Complex.normSq_apply]
      have hμ2 : μ.re ^ 2 + μ.im ^ 2 ≤ M ^ 2 := by
        have := Complex.sq_norm μ
        rw [Complex.normSq_apply] at this
        nlinarith [norm_nonneg μ]
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im]
      have e : m ^ 2 / M ^ 2 = 2 * h * m - h ^ 2 * M ^ 2 := by
        rw [hhdef]; field_simp; ring
      rw [e]
      nlinarith [sq_nonneg h, hh]
    have hn0 := norm_nonneg z
    rw [hqdef]; nlinarith [sq_nonneg (1 - ‖z‖)]
  set q' : NNReal := ⟨q, hq0⟩ with hq'
  have hrad : spectralRadius ℂ Bℂ ≤ (q' : ENNReal) := by
    refine iSup₂_le fun z hz => ?_
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
    exact hspec z hz
  set r : NNReal := ⟨(q + 1) / 2, by linarith⟩ with hr
  have hr1 : (r : ℝ) < 1 := by change (q + 1) / 2 < 1; linarith
  have hqr : spectralRadius ℂ Bℂ < (r : ENNReal) := by
    refine lt_of_le_of_lt hrad ?_
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
    change q < (q + 1) / 2; linarith
  have hG := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius Bℂ
  have hev1 := hG.eventually (gt_mem_nhds hqr)
  obtain ⟨C, hC0, hC⟩ := aux_pj_matNorm_le_linfty N
  have hev2 : ∀ᶠ n : ℕ in atTop, C * (r : ℝ) ^ n ≤ 1 / 2 := by
    have : Tendsto (fun n : ℕ => C * (r : ℝ) ^ n) atTop (𝓝 (C * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one r.2 hr1).const_mul C
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  obtain ⟨L, ⟨hL1, hL2⟩, hL3⟩ := ((hev1.and hev2).and (eventually_ge_atTop 1)).exists
  refine ⟨h, hh, L, hL3, ?_⟩
  have hL1' : ‖Bℂ ^ L‖₊ < r ^ L := by
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL3
    rw [one_div, ENNReal.rpow_inv_lt_iff hLpos, ENNReal.rpow_natCast] at hL1
    exact_mod_cast hL1
  have hL1'' : ‖Bℂ ^ L‖ ≤ (r : ℝ) ^ L := by
    rw [← coe_nnnorm]; exact_mod_cast hL1'.le
  have hmapL : (B ^ L).map (algebraMap ℝ ℂ) = Bℂ ^ L := by
    rw [hBℂ]; exact ((algebraMap ℝ ℂ).mapMatrix.map_pow B L)
  have hnormeq : ‖(B ^ L).map (algebraMap ℝ ℂ)‖ = ‖B ^ L‖ := by
    simp [Matrix.linfty_opNorm_def]
  calc matNorm (B ^ L) ≤ C * ‖B ^ L‖ := hC _
    _ = C * ‖Bℂ ^ L‖ := by rw [← hnormeq, hmapL]
    _ ≤ C * (r : ℝ) ^ L := mul_le_mul_of_nonneg_left hL1'' hC0
    _ ≤ 1 / 2 := hL2

lemma aux_pj_mn_nonneg {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) : 0 ≤ matNorm M := norm_nonneg _

lemma aux_pj_mn_mul {N : ℕ} (M M' : Matrix (Fin N) (Fin N) ℝ) :
    matNorm (M * M') ≤ matNorm M * matNorm M' := by
  unfold matNorm; rw [map_mul]; exact norm_mul_le _ _

lemma aux_pj_mn_add {N : ℕ} (M M' : Matrix (Fin N) (Fin N) ℝ) :
    matNorm (M + M') ≤ matNorm M + matNorm M' := by
  unfold matNorm; rw [map_add]; exact norm_add_le _ _

lemma aux_pj_mn_sub {N : ℕ} (M M' : Matrix (Fin N) (Fin N) ℝ) :
    matNorm (M - M') ≤ matNorm M + matNorm M' := by
  unfold matNorm; rw [map_sub]; exact norm_sub_le _ _

lemma aux_pj_mn_smul {N : ℕ} (a : ℝ) (M : Matrix (Fin N) (Fin N) ℝ) :
    matNorm (a • M) = |a| * matNorm M := by
  unfold matNorm; rw [map_smul, norm_smul, Real.norm_eq_abs]

lemma aux_pj_mn_sum {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin N) (Fin N) ℝ) :
    matNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, matNorm (f i) := by
  unfold matNorm; rw [map_sum]; exact norm_sum_le _ _

lemma aux_pj_mn_one {N : ℕ} : matNorm (1 : Matrix (Fin N) (Fin N) ℝ) ≤ 1 := by
  unfold matNorm; rw [map_one]; exact ContinuousLinearMap.norm_id_le

lemma aux_pj_X_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) {j i : ℕ} (h : i ≤ j) :
    lemX A γ j i = 1 := by
  cases i with
  | zero => rfl
  | succ i => simp only [lemX]; rw [if_neg (by omega)]

lemma aux_pj_X_succ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) {j i : ℕ} (h : j ≤ i) :
    lemX A γ j (i + 1) = (1 - γ i • A) * lemX A γ j i := by
  simp only [lemX]; rw [if_pos h, sub_mul, one_mul, smul_mul_assoc]

lemma aux_pj_contr {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : EigenRePos A) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ h : ℝ, 0 < h ∧ ∀ (γ : ℕ → ℝ) (j i : ℕ), j ≤ i →
      (∀ k ∈ Finset.Ico j i, 0 ≤ γ k ∧ γ k ≤ h) →
      matNorm (lemX A γ j i) ≤ C * Real.exp (-(c * ∑ k ∈ Finset.Ico j i, γ k)) := by
  obtain ⟨h, hh, L, hL1, hL⟩ := aux_pj_spec A hA
  set B : Matrix (Fin N) (Fin N) ℝ := 1 - h • A with hB
  let nrm : Matrix (Fin N) (Fin N) ℝ → ℝ := fun M => ∑ n ∈ Finset.range L, matNorm (B ^ n * M)
  set C0 : ℝ := ∑ n ∈ Finset.range L, matNorm (B ^ n) with hC0
  have hC0nn : 0 ≤ C0 := Finset.sum_nonneg fun n _ => aux_pj_mn_nonneg _
  set C' : ℝ := C0 + 1 with hC'
  have hC'pos : 0 < C' := by linarith
  have nrm_ge : ∀ M, matNorm M ≤ nrm M := by
    intro M
    have := Finset.single_le_sum (f := fun n => matNorm (B ^ n * M))
      (fun n _ => aux_pj_mn_nonneg _) (Finset.mem_range.mpr (by omega : 0 < L))
    simpa using this
  have nrm_le : ∀ M, nrm M ≤ C0 * matNorm M := by
    intro M
    rw [hC0, Finset.sum_mul]
    exact Finset.sum_le_sum fun n _ => aux_pj_mn_mul _ _
  have nrm_le' : ∀ M, nrm M ≤ C' * matNorm M := by
    intro M; have := nrm_le M; have := aux_pj_mn_nonneg M; nlinarith
  have nrm_nn : ∀ M, 0 ≤ nrm M := fun M => Finset.sum_nonneg fun n _ => aux_pj_mn_nonneg _
  have nrm_add : ∀ M M', nrm (M + M') ≤ nrm M + nrm M' := by
    intro M M'
    simp only [nrm, ← Finset.sum_add_distrib, mul_add]
    exact Finset.sum_le_sum fun n _ => aux_pj_mn_add _ _
  have nrm_smul : ∀ (a : ℝ) M, nrm (a • M) = |a| * nrm M := by
    intro a M
    simp only [nrm, Finset.mul_sum, mul_smul_comm, aux_pj_mn_smul]
  have nrm_B : ∀ M, nrm (B * M) ≤ nrm M - matNorm M / 2 := by
    intro M
    have e1 := Finset.sum_range_succ (fun n => matNorm (B ^ n * M)) L
    have e2 := Finset.sum_range_succ' (fun n => matNorm (B ^ n * M)) L
    have e3 : nrm (B * M) = ∑ n ∈ Finset.range L, matNorm (B ^ (n + 1) * M) := by
      simp only [nrm, ← mul_assoc, ← pow_succ]
    have hBL : matNorm (B ^ L * M) ≤ 1 / 2 * matNorm M :=
      (aux_pj_mn_mul _ _).trans (mul_le_mul_of_nonneg_right hL (aux_pj_mn_nonneg _))
    simp only [pow_zero, one_mul] at e2
    have : nrm M = ∑ n ∈ Finset.range L, matNorm (B ^ n * M) := rfl
    linarith
  set c : ℝ := 1 / (2 * h * C') with hc
  have hcpos : 0 < c := by positivity
  have step : ∀ (g : ℝ) M, 0 ≤ g → g ≤ h → nrm ((1 - g • A) * M) ≤ (1 - c * g) * nrm M := by
    intro g M hg0 hgh
    have e : (1 - g • A) * M = (1 - g / h) • M + (g / h) • (B * M) := by
      rw [hB]
      simp only [sub_mul, one_mul, smul_mul_assoc]
      rw [smul_sub, smul_smul, div_mul_cancel₀ _ hh.ne', sub_smul, one_smul]
      abel
    rw [e]
    have hgh' : g / h ≤ 1 := (div_le_one hh).mpr hgh
    have hg' : 0 ≤ g / h := div_nonneg hg0 hh.le
    refine (nrm_add _ _).trans ?_
    rw [nrm_smul, nrm_smul, abs_of_nonneg (by linarith), abs_of_nonneg hg']
    have h1 := nrm_B M
    have h2 := nrm_le' M
    have h3 : c * g * nrm M ≤ g / h * (matNorm M / 2) := by
      rw [hc]
      have : nrm M / C' ≤ matNorm M := by rw [div_le_iff₀ hC'pos]; linarith
      calc 1 / (2 * h * C') * g * nrm M = g / h * ((nrm M / C') / 2) := by
            field_simp
        _ ≤ g / h * (matNorm M / 2) := by gcongr
    nlinarith
  refine ⟨c, hcpos, C', hC'pos, h, hh, fun γ j i hji hγ => ?_⟩
  have key : ∀ i, j ≤ i → (∀ k ∈ Finset.Ico j i, 0 ≤ γ k ∧ γ k ≤ h) →
      nrm (lemX A γ j i) ≤ Real.exp (-(c * ∑ k ∈ Finset.Ico j i, γ k)) * nrm 1 := by
    intro i hji
    induction i, hji using Nat.le_induction with
    | base => intro _; rw [aux_pj_X_le A γ le_rfl]; simp
    | succ i hji ih =>
      intro hγ'
      have hγi := hγ' i (Finset.mem_Ico.mpr ⟨hji, by omega⟩)
      have ih' := ih (fun k hk => hγ' k (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hk).1,
        by have := (Finset.mem_Ico.mp hk).2; omega⟩))
      rw [aux_pj_X_succ A γ hji, Finset.sum_Ico_succ_top hji]
      refine (step _ _ hγi.1 hγi.2).trans ?_
      have hex : 1 - c * γ i ≤ Real.exp (-(c * γ i)) := by
        have := Real.add_one_le_exp (-(c * γ i)); linarith
      calc (1 - c * γ i) * nrm (lemX A γ j i)
          ≤ Real.exp (-(c * γ i)) * nrm (lemX A γ j i) :=
            mul_le_mul_of_nonneg_right hex (nrm_nn _)
        _ ≤ Real.exp (-(c * γ i)) * (Real.exp (-(c * ∑ k ∈ Finset.Ico j i, γ k)) * nrm 1) :=
            mul_le_mul_of_nonneg_left ih' (Real.exp_pos _).le
        _ = _ := by rw [← mul_assoc, ← Real.exp_add]; ring_nf
  have k1 := key i hji hγ
  have k2 : nrm 1 ≤ C' := by
    have := nrm_le' 1; have := aux_pj_mn_one (N := N); nlinarith
  calc matNorm (lemX A γ j i) ≤ nrm (lemX A γ j i) := nrm_ge _
    _ ≤ Real.exp (-(c * ∑ k ∈ Finset.Ico j i, γ k)) * nrm 1 := k1
    _ ≤ Real.exp (-(c * ∑ k ∈ Finset.Ico j i, γ k)) * C' :=
        mul_le_mul_of_nonneg_left k2 (Real.exp_pos _).le
    _ = _ := mul_comm _ _

lemma aux_pj_inv {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : EigenRePos A) :
    A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 := by
  have h0 : (0:ℂ) ∉ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := fun h => by
    have := hA 0 h; simp at this
  rw [spectrum.zero_mem_iff, not_not, Matrix.isUnit_iff_isUnit_det] at h0
  have hdet : IsUnit A.det := by
    rw [isUnit_iff_ne_zero] at h0 ⊢
    intro hd; apply h0
    have := RingHom.map_det (algebraMap ℝ ℂ) A
    rw [hd, map_zero] at this
    exact this.symm
  exact ⟨Matrix.mul_nonsing_inv A hdet, Matrix.nonsing_inv_mul A hdet⟩

lemma aux_pj_sumX {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j : ℕ) :
    ∀ t, j ≤ t → A * ∑ i ∈ Finset.Ico j t, γ i • lemX A γ j i = 1 - lemX A γ j t := by
  intro t hjt
  induction t, hjt using Nat.le_induction with
  | base => simp [aux_pj_X_le A γ le_rfl]
  | succ t hjt ih =>
    rw [Finset.sum_Ico_succ_top hjt, mul_add, ih, aux_pj_X_succ A γ hjt, mul_smul_comm]
    rw [sub_mul, one_mul, smul_mul_assoc]
    abel

lemma aux_pj_phi_id {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (hinv : A⁻¹ * A = 1)
    (j t : ℕ) (hjt : j ≤ t) :
    lemPhi A γ j t = A⁻¹ * lemX A γ j t - ∑ i ∈ Finset.Ico j t, (γ j - γ i) • lemX A γ j i := by
  have hS : ∑ i ∈ Finset.Ico j t, γ i • lemX A γ j i = A⁻¹ - A⁻¹ * lemX A γ j t := by
    have := congrArg (A⁻¹ * ·) (aux_pj_sumX A γ j t hjt)
    simp only [← mul_assoc, hinv, one_mul, mul_sub, mul_one] at this
    exact this
  unfold lemPhi lemXbar
  have e : γ j • ∑ i ∈ Finset.Ico j t, lemX A γ j i = ∑ i ∈ Finset.Ico j t, γ i • lemX A γ j i +
      ∑ i ∈ Finset.Ico j t, (γ j - γ i) • lemX A γ j i := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul]; congr 1; ring
  rw [e, hS]; abel

lemma aux_pj_small (γ : ℕ → ℝ) (hγ : StepCondition4 γ) (H : ℝ) (hH : 0 < H) :
    ∃ J, ∀ k ≥ J, γ k ≤ H := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hγ.2.1.eventually (gt_mem_nhds hH))
  exact ⟨J, fun k hk => (hJ k hk).le⟩

lemma aux_pj_diff (γ : ℕ → ℝ) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ) (δ : ℝ)
    (hδ : 0 < δ) : ∃ J, ∀ k ≥ J, |γ k - γ (k + 1)| ≤ δ * γ k ^ 2 := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hγ.2.2.def hδ)
  refine ⟨J, fun k hk => ?_⟩
  have := hJ k hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos (hpos k),
    div_le_iff₀ (hpos k)] at this
  rw [sq, ← mul_assoc]; exact this

lemma aux_pj_tgamma (γ : ℕ → ℝ) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ) :
    Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * (γ t)⁻¹) atTop (𝓝 0) := by
  set d : ℕ → ℝ := fun k => (γ (k + 1))⁻¹ - (γ k)⁻¹ with hd
  have hdt : Tendsto d atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]; intro ε hε
    obtain ⟨J1, hJ1⟩ := aux_pj_diff γ hpos hγ (ε / 4) (by positivity)
    obtain ⟨J2, hJ2⟩ := aux_pj_small γ hγ (2 / ε) (by positivity)
    refine ⟨max J1 J2, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero]
    have g0 := hpos k
    have g1 := hpos (k + 1)
    have hdiff := hJ1 k (le_of_max_le_left hk)
    have hsm := hJ2 k (le_of_max_le_right hk)
    have hsm' : ε * γ k ≤ 2 := by rw [le_div_iff₀ hε] at hsm; linarith
    have hg1 : γ k / 2 ≤ γ (k + 1) := by
      have := (abs_le.mp hdiff).2
      nlinarith
    simp only [hd]
    rw [inv_sub_inv g1.ne' g0.ne', abs_div, abs_of_pos (mul_pos g1 g0),
      div_lt_iff₀ (mul_pos g1 g0)]
    calc |γ k - γ (k + 1)| ≤ ε / 4 * γ k ^ 2 := hdiff
      _ < ε * (γ (k + 1) * γ k) := by
        have h1 : ε * γ k * (γ k / 2) ≤ ε * γ k * γ (k + 1) :=
          mul_le_mul_of_nonneg_left hg1 (by positivity)
        have h2 : 0 < ε * γ k * γ k := by positivity
        nlinarith
  have hc := hdt.cesaro
  have hsum : ∀ t, ∑ k ∈ Finset.range t, d k = (γ t)⁻¹ - (γ 0)⁻¹ :=
    fun t => Finset.sum_range_sub (fun k => (γ k)⁻¹) t
  have h2 : Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * (γ 0)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (γ 0)⁻¹
    simpa using this
  have h3 := hc.add h2
  simp only [hsum, zero_add] at h3
  refine h3.congr (fun t => ?_)
  ring

lemma aux_pj_ratio (γ : ℕ → ℝ) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ) (H : ℝ)
    (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) :
    ∃ J, (∀ k ≥ J, γ k ≤ H) ∧ ∀ j ≥ J, ∀ i ≥ j,
      γ i ≤ γ j * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k) ∧
      γ j ≤ γ i * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k) := by
  obtain ⟨J1, hJ1⟩ := aux_pj_diff γ hpos hγ δ hδ
  obtain ⟨J2, hJ2⟩ := aux_pj_small γ hγ (min H (1 / (2 * δ))) (by positivity)
  refine ⟨max J1 J2, fun k hk => (hJ2 k (le_of_max_le_right hk)).trans (min_le_left _ _),
    fun j hj i hij => ?_⟩
  have step : ∀ k ≥ max J1 J2, γ (k + 1) ≤ γ k * Real.exp (2 * δ * γ k) ∧
      γ k ≤ γ (k + 1) * Real.exp (2 * δ * γ k) := by
    intro k hk
    have hd := abs_le.mp (hJ1 k (le_of_max_le_left hk))
    have hs : γ k ≤ 1 / (2 * δ) := (hJ2 k (le_of_max_le_right hk)).trans (min_le_right _ _)
    have hx : δ * γ k ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hs; nlinarith
    have e1 := Real.add_one_le_exp (2 * δ * γ k)
    have g0 := hpos k
    have hδg : 0 ≤ δ * γ k := by positivity
    constructor
    · nlinarith
    · have : γ k * (1 - δ * γ k) ≤ γ (k + 1) := by nlinarith
      have h2 : γ k ≤ γ k * (1 - δ * γ k) * (2 * δ * γ k + 1) := by nlinarith
      have h3 : γ k * (1 - δ * γ k) * (2 * δ * γ k + 1) ≤ γ (k + 1) * Real.exp (2 * δ * γ k) := by
        apply mul_le_mul this e1 (by positivity) (hpos _).le
      linarith
  induction i, hij using Nat.le_induction with
  | base => simp
  | succ i hji ih =>
    rw [Finset.sum_Ico_succ_top hji, mul_add, Real.exp_add]
    obtain ⟨s1, s2⟩ := step i (le_trans hj hji)
    obtain ⟨ih1, ih2⟩ := ih
    have ep1 := Real.exp_pos (2 * δ * γ i)
    have ep2 := Real.exp_pos (2 * δ * ∑ k ∈ Finset.Ico j i, γ k)
    constructor
    · calc γ (i + 1) ≤ γ i * Real.exp (2 * δ * γ i) := s1
        _ ≤ γ j * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k) * Real.exp (2 * δ * γ i) :=
          mul_le_mul_of_nonneg_right ih1 ep1.le
        _ = _ := by ring
    · calc γ j ≤ γ i * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k) := ih2
        _ ≤ γ (i + 1) * Real.exp (2 * δ * γ i) * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k) :=
          mul_le_mul_of_nonneg_right s2 ep2.le
        _ = _ := by ring

lemma aux_pj_keyexp (b H g : ℝ) (hb : 0 < b) (hg : 0 ≤ g) (hgH : g ≤ H) :
    g ≤ (1 + b * H) / b * (1 - Real.exp (-(b * g))) := by
  have e1 := Real.add_one_le_exp (b * g)
  have e2 : Real.exp (-(b * g)) * Real.exp (b * g) = 1 := by rw [← Real.exp_add]; simp
  have e3 : Real.exp (-(b * g)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e4 := Real.exp_pos (-(b * g))
  rw [div_mul_eq_mul_div, le_div_iff₀ hb]
  have h1 : Real.exp (-(b * g)) * (b * g + 1) ≤ Real.exp (-(b * g)) * Real.exp (b * g) :=
    mul_le_mul_of_nonneg_left e1 e4.le
  have h2 : 0 ≤ (b * H - b * g) * (1 - Real.exp (-(b * g))) :=
    mul_nonneg (by nlinarith) (by linarith)
  nlinarith

lemma aux_pj_tele_fwd (γ : ℕ → ℝ) (b H : ℝ) (hb : 0 < b) (hH : 0 ≤ H) (j : ℕ)
    (hγ : ∀ k ≥ j, 0 ≤ γ k ∧ γ k ≤ H) (t : ℕ) :
    ∑ i ∈ Finset.Ico j t, γ i * Real.exp (-(b * ∑ k ∈ Finset.Ico j i, γ k)) ≤ (1 + b * H) / b := by
  have hK : 0 ≤ (1 + b * H) / b := by positivity
  rcases lt_or_ge t j with htj | hjt
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; exact hK
  have key : ∀ t, j ≤ t → ∑ i ∈ Finset.Ico j t, γ i * Real.exp (-(b * ∑ k ∈ Finset.Ico j i, γ k))
      ≤ (1 + b * H) / b * (1 - Real.exp (-(b * ∑ k ∈ Finset.Ico j t, γ k))) := by
    intro t hjt
    induction t, hjt using Nat.le_induction with
    | base => simp
    | succ t hjt ih =>
      rw [Finset.sum_Ico_succ_top hjt, Finset.sum_Ico_succ_top hjt, mul_add, neg_add,
        Real.exp_add]
      have hk := aux_pj_keyexp b H (γ t) hb (hγ t hjt).1 (hγ t hjt).2
      have ep := Real.exp_pos (-(b * ∑ k ∈ Finset.Ico j t, γ k))
      have : γ t * Real.exp (-(b * ∑ k ∈ Finset.Ico j t, γ k)) ≤
          (1 + b * H) / b * (1 - Real.exp (-(b * γ t))) *
            Real.exp (-(b * ∑ k ∈ Finset.Ico j t, γ k)) := mul_le_mul_of_nonneg_right hk ep.le
      nlinarith
  refine (key t hjt).trans ?_
  have := Real.exp_pos (-(b * ∑ k ∈ Finset.Ico j t, γ k))
  nlinarith

lemma aux_pj_tele_bwd (γ : ℕ → ℝ) (b H : ℝ) (hb : 0 < b) (hH : 0 ≤ H) (J : ℕ)
    (hγ : ∀ k ≥ J, 0 ≤ γ k ∧ γ k ≤ H) (t : ℕ) :
    ∑ j ∈ Finset.Ico J t, γ j * Real.exp (-(b * ∑ k ∈ Finset.Ico j t, γ k)) ≤ (1 + b * H) / b := by
  have hK : 0 ≤ (1 + b * H) / b := by positivity
  rcases lt_or_ge t J with htj | hjt
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; exact hK
  induction t, hjt using Nat.le_induction with
  | base => simp; exact hK
  | succ t hjt ih =>
    rw [Finset.sum_Ico_succ_top hjt]
    have e : ∀ j ∈ Finset.Ico J t, γ j * Real.exp (-(b * ∑ k ∈ Finset.Ico j (t + 1), γ k)) =
        Real.exp (-(b * γ t)) * (γ j * Real.exp (-(b * ∑ k ∈ Finset.Ico j t, γ k))) := by
      intro j hj
      rw [Finset.sum_Ico_succ_top (Finset.mem_Ico.mp hj).2.le, mul_add, neg_add, Real.exp_add]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_Ico_succ_top le_rfl,
      Finset.Ico_self, Finset.sum_empty, zero_add]
    have ih' := ih
    have hk := aux_pj_keyexp b H (γ t) hb (hγ t hjt).1 (hγ t hjt).2
    have e3 : Real.exp (-(b * γ t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [(hγ t hjt).1])
    have e4 := Real.exp_pos (-(b * γ t))
    have g0 := (hγ t hjt).1
    nlinarith

lemma aux_pj_pt (δ c C S gj gi x : ℝ) (hδ : 0 ≤ δ) (hδc : δ ≤ c / 8) (hc : 0 < c)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hgi : 0 ≤ gi) (hgj : 0 ≤ gj)
    (r1 : gi ≤ gj * Real.exp (2 * δ * S)) (r2 : gj ≤ gi * Real.exp (2 * δ * S))
    (hx0 : 0 ≤ x) (hx : x ≤ C * Real.exp (-(c * S))) :
    |gj - gi| * x ≤ δ * (8 * C / c) * (gi * Real.exp (-(c / 4 * S))) := by
  set u := Real.exp (2 * δ * S) with hu
  have hu1 : 1 ≤ u := Real.one_le_exp (by positivity)
  have ha : |gj - gi| ≤ gi * u * (u - 1) := by
    rcases le_total gi gj with h | h
    · rw [abs_of_nonneg (by linarith)]
      have : 0 ≤ gi * (u - 1) * (u - 1) := by
        have : 0 ≤ u - 1 := by linarith
        positivity
      nlinarith
    · rw [abs_of_nonpos (by linarith)]
      have : gj * (u - 1) ≤ gi * u * (u - 1) := mul_le_mul_of_nonneg_right r2 (by linarith)
      nlinarith
  have hb : u - 1 ≤ 2 * δ * S * u := by
    have h1 := Real.add_one_le_exp (-(2 * δ * S))
    have e : Real.exp (-(2 * δ * S)) * u = 1 := by rw [hu, ← Real.exp_add]; simp
    nlinarith
  have hc2 : u * u * Real.exp (-(c * S)) ≤ Real.exp (-(c / 2 * S)) := by
    rw [hu, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr; nlinarith
  have hd : S * Real.exp (-(c / 2 * S)) ≤ 4 / c * Real.exp (-(c / 4 * S)) := by
    have h1 := Real.add_one_le_exp (c / 4 * S)
    have e1 : Real.exp (-(c / 4 * S)) * Real.exp (c / 4 * S) = 1 := by
      rw [← Real.exp_add]; simp
    have e2 : Real.exp (-(c / 2 * S)) = Real.exp (-(c / 4 * S)) * Real.exp (-(c / 4 * S)) := by
      rw [← Real.exp_add]; ring_nf
    have ep := Real.exp_pos (-(c / 4 * S))
    have h3 : S * Real.exp (-(c / 4 * S)) ≤ 4 / c := by
      rw [le_div_iff₀ hc]
      have : S * Real.exp (-(c / 4 * S)) * c = 4 * (Real.exp (-(c / 4 * S)) * (c / 4 * S)) := by
        ring
      rw [this]
      have : Real.exp (-(c / 4 * S)) * (c / 4 * S) ≤ Real.exp (-(c / 4 * S)) * Real.exp (c / 4 * S) :=
        mul_le_mul_of_nonneg_left (by linarith) ep.le
      linarith
    rw [e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h3 ep.le
  have hu0 : 0 ≤ u := by linarith
  have hex := Real.exp_pos (-(c * S))
  calc |gj - gi| * x ≤ (gi * u * (u - 1)) * (C * Real.exp (-(c * S))) :=
        mul_le_mul ha hx hx0 (by have : 0 ≤ u - 1 := by linarith
                                 positivity)
    _ ≤ (gi * u * (2 * δ * S * u)) * (C * Real.exp (-(c * S))) := by gcongr
    _ = 2 * δ * C * gi * (S * (u * u * Real.exp (-(c * S)))) := by ring
    _ ≤ 2 * δ * C * gi * (S * Real.exp (-(c / 2 * S))) := by gcongr
    _ ≤ 2 * δ * C * gi * (4 / c * Real.exp (-(c / 4 * S))) := by gcongr
    _ = δ * (8 * C / c) * (gi * Real.exp (-(c / 4 * S))) := by field_simp; ring

lemma aux_pj_Dbound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (hpos : ∀ t, 0 < γ t)
    {c C h δ : ℝ} (hc : 0 < c) (hC : 0 < C) (hh : 0 < h) (hδ : 0 < δ) (hδc : δ ≤ c / 8)
    (hX : ∀ j i, j ≤ i → (∀ k ∈ Finset.Ico j i, 0 ≤ γ k ∧ γ k ≤ h) →
      matNorm (lemX A γ j i) ≤ C * Real.exp (-(c * ∑ k ∈ Finset.Ico j i, γ k)))
    (J : ℕ) (hJh : ∀ k ≥ J, γ k ≤ h)
    (hJr : ∀ j ≥ J, ∀ i ≥ j, γ i ≤ γ j * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k) ∧
      γ j ≤ γ i * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k))
    (j t : ℕ) (hj : J ≤ j) :
    ∑ i ∈ Finset.Ico j t, |γ j - γ i| * matNorm (lemX A γ j i) ≤
      δ * (8 * C / c * ((1 + c / 4 * h) / (c / 4))) := by
  have hγb : ∀ k ≥ j, 0 ≤ γ k ∧ γ k ≤ h := fun k hk => ⟨(hpos k).le, hJh k (le_trans hj hk)⟩
  calc ∑ i ∈ Finset.Ico j t, |γ j - γ i| * matNorm (lemX A γ j i)
      ≤ ∑ i ∈ Finset.Ico j t, δ * (8 * C / c) *
          (γ i * Real.exp (-(c / 4 * ∑ k ∈ Finset.Ico j i, γ k))) := by
        apply Finset.sum_le_sum; intro i hi
        have hji := (Finset.mem_Ico.mp hi).1
        obtain ⟨r1, r2⟩ := hJr j hj i hji
        exact aux_pj_pt δ c C _ (γ j) (γ i) _ hδ.le hδc hc hC.le
          (Finset.sum_nonneg fun k _ => (hpos k).le) (hpos i).le (hpos j).le r1 r2
          (aux_pj_mn_nonneg _)
          (hX j i hji (fun k hk => hγb k (Finset.mem_Ico.mp hk).1))
    _ = δ * (8 * C / c) * ∑ i ∈ Finset.Ico j t,
          γ i * Real.exp (-(c / 4 * ∑ k ∈ Finset.Ico j i, γ k)) := by rw [Finset.mul_sum]
    _ ≤ δ * (8 * C / c) * ((1 + c / 4 * h) / (c / 4)) :=
        mul_le_mul_of_nonneg_left (aux_pj_tele_fwd γ (c / 4) h (by positivity) hh.le j hγb t)
          (by positivity)
    _ = _ := by ring

lemma aux_pj_Xavg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (hpos : ∀ t, 0 < γ t)
    {c C h δ : ℝ} (hc : 0 < c) (hC : 0 < C) (hh : 0 < h) (hδ : 0 < δ) (hδc : δ ≤ c / 8)
    (hX : ∀ j i, j ≤ i → (∀ k ∈ Finset.Ico j i, 0 ≤ γ k ∧ γ k ≤ h) →
      matNorm (lemX A γ j i) ≤ C * Real.exp (-(c * ∑ k ∈ Finset.Ico j i, γ k)))
    (J : ℕ) (hJh : ∀ k ≥ J, γ k ≤ h)
    (hJr : ∀ j ≥ J, ∀ i ≥ j, γ i ≤ γ j * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k) ∧
      γ j ≤ γ i * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k))
    (t : ℕ) :
    ∑ j ∈ Finset.Ico J t, matNorm (lemX A γ j t) ≤
      C * (γ t)⁻¹ * ((1 + c / 4 * h) / (c / 4)) := by
  have hγb : ∀ k ≥ J, 0 ≤ γ k ∧ γ k ≤ h := fun k hk => ⟨(hpos k).le, hJh k hk⟩
  calc ∑ j ∈ Finset.Ico J t, matNorm (lemX A γ j t)
      ≤ ∑ j ∈ Finset.Ico J t, C * (γ t)⁻¹ *
          (γ j * Real.exp (-(c / 4 * ∑ k ∈ Finset.Ico j t, γ k))) := by
        apply Finset.sum_le_sum; intro j hj
        obtain ⟨hJj, hjt⟩ := Finset.mem_Ico.mp hj
        have hx := hX j t hjt.le (fun k hk => ⟨(hpos k).le,
          hJh k (by have := (Finset.mem_Ico.mp hk).1; omega)⟩)
        obtain ⟨r1, -⟩ := hJr j hJj t hjt.le
        refine hx.trans ?_
        have hS : 0 ≤ ∑ k ∈ Finset.Ico j t, γ k := Finset.sum_nonneg fun k _ => (hpos k).le
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hC.le
        rw [le_inv_mul_iff₀ (hpos t)]
        calc γ t * Real.exp (-(c * ∑ k ∈ Finset.Ico j t, γ k))
            ≤ γ j * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j t, γ k) *
                Real.exp (-(c * ∑ k ∈ Finset.Ico j t, γ k)) :=
              mul_le_mul_of_nonneg_right r1 (Real.exp_pos _).le
          _ = γ j * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j t, γ k +
                -(c * ∑ k ∈ Finset.Ico j t, γ k)) := by rw [mul_assoc, ← Real.exp_add]
          _ ≤ γ j * Real.exp (-(c / 4 * ∑ k ∈ Finset.Ico j t, γ k)) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (hpos j).le
    _ = C * (γ t)⁻¹ * ∑ j ∈ Finset.Ico J t,
          γ j * Real.exp (-(c / 4 * ∑ k ∈ Finset.Ico j t, γ k)) := by rw [Finset.mul_sum]
    _ ≤ C * (γ t)⁻¹ * ((1 + c / 4 * h) / (c / 4)) :=
        mul_le_mul_of_nonneg_left (aux_pj_tele_bwd γ (c / 4) h (by positivity) hh.le J hγb t)
          (by have := hpos t; positivity)

end PolyakJuditsky.Averaging

open PolyakJuditsky.Averaging

theorem solution {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ)
    (hA : EigenRePos A) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ) :
    ∃ K : ℝ, (∀ j t, j ≤ t → matNorm (lemPhi A γ j t) ≤ K) ∧
      Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * ∑ j ∈ Finset.range t, matNorm (lemPhi A γ j t))
        atTop (𝓝 0) := by
  obtain ⟨-, hinv⟩ := aux_pj_inv A hA
  obtain ⟨c, hc, C, hC, h, hh, hX'⟩ := aux_pj_contr A hA
  have hX := hX' γ
  set α := matNorm A⁻¹ with hα
  have hα0 : 0 ≤ α := aux_pj_mn_nonneg _
  set Kb := (1 + c / 4 * h) / (c / 4) with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  set E := 8 * C / c * Kb with hE
  have hE0 : 0 ≤ E := by positivity
  have hgood : ∀ δ, 0 < δ → δ ≤ c / 8 → ∀ J, (∀ k ≥ J, γ k ≤ h) →
      (∀ j ≥ J, ∀ i ≥ j, γ i ≤ γ j * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k) ∧
        γ j ≤ γ i * Real.exp (2 * δ * ∑ k ∈ Finset.Ico j i, γ k)) →
      ∀ j t, J ≤ j → j ≤ t → matNorm (lemPhi A γ j t) ≤ α * matNorm (lemX A γ j t) + δ * E := by
    intro δ hδ hδc J hJh hJr j t hj hjt
    rw [aux_pj_phi_id A γ hinv j t hjt]
    refine (aux_pj_mn_sub _ _).trans (add_le_add (aux_pj_mn_mul _ _) ?_)
    refine (aux_pj_mn_sum _ _).trans ?_
    simp_rw [aux_pj_mn_smul]
    exact aux_pj_Dbound A γ hpos hc hC hh hδ hδc hX J hJh hJr j t hj
  obtain ⟨J0, hJ0h, hJ0r⟩ := aux_pj_ratio γ hpos hγ h hh (c / 8) (by positivity)
  set K1 := α * C + c / 8 * E with hK1
  have hK1nn : 0 ≤ K1 := by positivity
  have hK1b : ∀ j t, J0 ≤ j → j ≤ t → matNorm (lemPhi A γ j t) ≤ K1 := by
    intro j t hj hjt
    refine (hgood (c / 8) (by positivity) le_rfl J0 hJ0h hJ0r j t hj hjt).trans ?_
    have hx := hX j t hjt (fun k hk => ⟨(hpos k).le,
      hJ0h k (by have := (Finset.mem_Ico.mp hk).1; omega)⟩)
    have hS : 0 ≤ ∑ k ∈ Finset.Ico j t, γ k := Finset.sum_nonneg fun k _ => (hpos k).le
    have h1 : Real.exp (-(c * ∑ k ∈ Finset.Ico j t, γ k)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : matNorm (lemX A γ j t) ≤ C := by nlinarith
    have h3 : α * matNorm (lemX A γ j t) ≤ α * C := mul_le_mul_of_nonneg_left h2 hα0
    linarith
  have hsplitX : ∀ j i, j ≤ J0 → J0 ≤ i → lemX A γ j i = lemX A γ J0 i * lemX A γ j J0 := by
    intro j i hj hi
    induction i, hi using Nat.le_induction with
    | base => rw [aux_pj_X_le A γ le_rfl, one_mul]
    | succ i hi ih =>
      rw [aux_pj_X_succ A γ (le_trans hj hi), aux_pj_X_succ A γ hi, ih, mul_assoc]
  have hsplit : ∀ j t, j ≤ J0 → J0 ≤ t → lemPhi A γ j t = lemPhi A γ j J0 -
      (γ j / γ J0) • ((A⁻¹ - lemPhi A γ J0 t) * lemX A γ j J0) := by
    intro j t hj ht
    have e1 : A⁻¹ - lemPhi A γ J0 t = lemXbar A γ J0 t := by unfold lemPhi; abel
    rw [e1]
    unfold lemPhi lemXbar
    rw [← Finset.sum_Ico_consecutive _ hj ht, smul_add]
    have : ∑ i ∈ Finset.Ico J0 t, lemX A γ j i =
        (∑ i ∈ Finset.Ico J0 t, lemX A γ J0 i) * lemX A γ j J0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i hi => hsplitX j i hj (Finset.mem_Ico.mp hi).1
    rw [this, smul_mul_assoc, smul_smul, div_mul_cancel₀ _ (hpos J0).ne']
    abel
  set S1 := ∑ j ∈ Finset.range J0, ∑ t ∈ Finset.range (J0 + 1), matNorm (lemPhi A γ j t)
    with hS1
  set S2 := ∑ j ∈ Finset.range J0, γ j / γ J0 * (α + K1) * matNorm (lemX A γ j J0) with hS2
  have hS1nn : 0 ≤ S1 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun t _ => aux_pj_mn_nonneg _
  have hterm_nn : ∀ j, 0 ≤ γ j / γ J0 * (α + K1) * matNorm (lemX A γ j J0) := by
    intro j
    have := hpos j; have := hpos J0; have := aux_pj_mn_nonneg (lemX A γ j J0)
    positivity
  have hS2nn : 0 ≤ S2 := Finset.sum_nonneg fun j _ => hterm_nn j
  have hK2a : ∀ j t, j < J0 → t ≤ J0 → matNorm (lemPhi A γ j t) ≤ S1 := by
    intro j t hj ht
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun j => ∑ t ∈ Finset.range (J0 + 1), matNorm (lemPhi A γ j t))
      (fun j _ => Finset.sum_nonneg fun t _ => aux_pj_mn_nonneg _) (Finset.mem_range.mpr hj))
    exact Finset.single_le_sum (f := fun t => matNorm (lemPhi A γ j t))
      (fun t _ => aux_pj_mn_nonneg _) (Finset.mem_range.mpr (by omega))
  have hK2b : ∀ j, j < J0 → γ j / γ J0 * (α + K1) * matNorm (lemX A γ j J0) ≤ S2 := by
    intro j hj
    exact Finset.single_le_sum
      (f := fun j => γ j / γ J0 * (α + K1) * matNorm (lemX A γ j J0))
      (fun j _ => hterm_nn j) (Finset.mem_range.mpr hj)
  set K := K1 + (S1 + S2) with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  have hbound : ∀ j t, j ≤ t → matNorm (lemPhi A γ j t) ≤ K := by
    intro j t hjt
    rcases le_or_gt J0 j with hj | hj
    · have := hK1b j t hj hjt; linarith
    · rcases le_or_gt t J0 with ht | ht
      · have := hK2a j t hj ht; linarith
      · rw [hsplit j t hj.le ht.le]
        have h1 := hK2a j J0 hj le_rfl
        have h2 := hK2b j hj
        have hq : 0 < γ j / γ J0 := div_pos (hpos j) (hpos J0)
        have h3 : matNorm ((γ j / γ J0) • ((A⁻¹ - lemPhi A γ J0 t) * lemX A γ j J0)) ≤
            γ j / γ J0 * (α + K1) * matNorm (lemX A γ j J0) := by
          rw [aux_pj_mn_smul, abs_of_pos hq, mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hq.le
          refine (aux_pj_mn_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (aux_pj_mn_nonneg _))
          exact (aux_pj_mn_sub _ _).trans (add_le_add le_rfl (hK1b J0 t le_rfl ht.le))
        have := aux_pj_mn_sub (lemPhi A γ j J0)
          ((γ j / γ J0) • ((A⁻¹ - lemPhi A γ J0 t) * lemX A γ j J0))
        linarith
  refine ⟨K, hbound, ?_⟩
  have havg_nn : ∀ t : ℕ, 0 ≤ (t : ℝ)⁻¹ * ∑ j ∈ Finset.range t, matNorm (lemPhi A γ j t) :=
    fun t => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun j _ => aux_pj_mn_nonneg _)
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun t => lt_of_lt_of_le ha (havg_nn t),
    fun ε hε => ?_⟩
  set δ := min (c / 8) (ε / (4 * (E + 1))) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδc : δ ≤ c / 8 := min_le_left _ _
  have hδE : δ * E ≤ ε / 4 := by
    have h1 : δ ≤ ε / (4 * (E + 1)) := min_le_right _ _
    calc δ * E ≤ ε / (4 * (E + 1)) * E := mul_le_mul_of_nonneg_right h1 hE0
      _ ≤ ε / 4 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  obtain ⟨J1, hJ1h, hJ1r⟩ := aux_pj_ratio γ hpos hγ h hh δ hδ
  have ht1 : Tendsto (fun t : ℕ => (J1 : ℝ) * K * (t : ℝ)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((J1 : ℝ) * K)
    simpa using this
  have ht2 : Tendsto (fun t : ℕ => α * C * Kb * ((t : ℝ)⁻¹ * (γ t)⁻¹)) atTop (𝓝 0) := by
    have := (aux_pj_tgamma γ hpos hγ).const_mul (α * C * Kb)
    simpa using this
  filter_upwards [ht1.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε / 4)),
    ht2.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε / 4)),
    eventually_ge_atTop (max J1 1)] with t h1 h2 h3
  have htJ : J1 ≤ t := le_of_max_le_left h3
  have htpos : (0 : ℝ) < t := by
    have := le_of_max_le_right h3
    exact_mod_cast this
  have hsum_split : ∑ j ∈ Finset.range t, matNorm (lemPhi A γ j t) =
      ∑ j ∈ Finset.range J1, matNorm (lemPhi A γ j t) +
        ∑ j ∈ Finset.Ico J1 t, matNorm (lemPhi A γ j t) :=
    (Finset.sum_range_add_sum_Ico _ htJ).symm
  have hA1 : ∑ j ∈ Finset.range J1, matNorm (lemPhi A γ j t) ≤ J1 * K := by
    calc ∑ j ∈ Finset.range J1, matNorm (lemPhi A γ j t) ≤ ∑ j ∈ Finset.range J1, K :=
          Finset.sum_le_sum fun j hj => hbound j t (by have := Finset.mem_range.mp hj; omega)
      _ = J1 * K := by simp
  have hXa : ∑ j ∈ Finset.Ico J1 t, matNorm (lemX A γ j t) ≤ C * (γ t)⁻¹ * Kb :=
    aux_pj_Xavg A γ hpos hc hC hh hδ hδc hX J1 hJ1h hJ1r t
  have hA2 : ∑ j ∈ Finset.Ico J1 t, matNorm (lemPhi A γ j t) ≤
      α * (C * (γ t)⁻¹ * Kb) + t * (δ * E) := by
    calc ∑ j ∈ Finset.Ico J1 t, matNorm (lemPhi A γ j t)
        ≤ ∑ j ∈ Finset.Ico J1 t, (α * matNorm (lemX A γ j t) + δ * E) :=
          Finset.sum_le_sum fun j hj => hgood δ hδ hδc J1 hJ1h hJ1r j t
            (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2.le
      _ = α * ∑ j ∈ Finset.Ico J1 t, matNorm (lemX A γ j t) + ((t : ℝ) - J1) * (δ * E) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico,
            nsmul_eq_mul, Nat.cast_sub htJ]
      _ ≤ α * (C * (γ t)⁻¹ * Kb) + t * (δ * E) := by
          have hJ1nn : (0 : ℝ) ≤ J1 := Nat.cast_nonneg _
          have hδE0 : 0 ≤ δ * E := by positivity
          have := mul_le_mul_of_nonneg_left hXa hα0
          nlinarith
  rw [hsum_split]
  have htinv : 0 ≤ (t : ℝ)⁻¹ := inv_nonneg.mpr htpos.le
  calc (t : ℝ)⁻¹ * (∑ j ∈ Finset.range J1, matNorm (lemPhi A γ j t) +
        ∑ j ∈ Finset.Ico J1 t, matNorm (lemPhi A γ j t))
      ≤ (t : ℝ)⁻¹ * (J1 * K + (α * (C * (γ t)⁻¹ * Kb) + t * (δ * E))) :=
        mul_le_mul_of_nonneg_left (add_le_add hA1 hA2) htinv
    _ = J1 * K * (t : ℝ)⁻¹ + α * C * Kb * ((t : ℝ)⁻¹ * (γ t)⁻¹) +
          (t : ℝ)⁻¹ * t * (δ * E) := by ring
    _ = J1 * K * (t : ℝ)⁻¹ + α * C * Kb * ((t : ℝ)⁻¹ * (γ t)⁻¹) + δ * E := by
        rw [inv_mul_cancel₀ htpos.ne', one_mul]
    _ < ε := by linarith
