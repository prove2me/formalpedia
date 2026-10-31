-- Prove2me | solution 1 for ShockCBM.ControlLimit.lemma_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:21:28.479956+00:00
-- url     : https://prove2.me/submissions/878fca40-747e-4de5-8a2a-36576d0559a9

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting
import Theorems.Thm_ShockCBM_ControlLimit_Enext_monotone_x

open MeasureTheory ShockCBM.ControlLimit

namespace ShockCBMD10

lemma ofReal_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)]
  · rw [integral_undef hi]; simp

lemma sum_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : ℕ → α → ENNReal)
    (N : ℕ) :
    ∑ i ∈ Finset.range N, ∫⁻ x, g i x ∂μ ≤ ∫⁻ x, ∑ i ∈ Finset.range N, g i x ∂μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    calc (∑ i ∈ Finset.range N, ∫⁻ x, g i x ∂μ) + ∫⁻ x, g N x ∂μ
        ≤ (∫⁻ x, ∑ i ∈ Finset.range N, g i x ∂μ) + ∫⁻ x, g N x ∂μ := by gcongr
      _ ≤ ∫⁻ x, (∑ i ∈ Finset.range N, g i x) + g N x ∂μ := le_lintegral_add _ _

lemma tsum_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : ℕ → α → ENNReal) :
    ∑' i, ∫⁻ x, g i x ∂μ ≤ ∫⁻ x, ∑' i, g i x ∂μ := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  exact (sum_lintegral_le μ g N).trans (lintegral_mono fun x => ENNReal.sum_le_tsum _)

open Finset in
lemma ennreal_cauchy (f g : ℕ → ENNReal) :
    ∑' z, ∑ j ∈ range (z+1), f j * g (z-j) = (∑' n, f n) * ∑' n, g n := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => f k * g l)]
  have h1 : ∀ n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 =
      ∑' x : (antidiagonal n), f x.1.1 * g x.1.2 := fun n => (Finset.tsum_subtype _ (fun kl : ℕ × ℕ => f kl.1 * g kl.2)).symm
  simp_rw [h1]
  have h2 := ENNReal.tsum_sigma' (β := fun n : ℕ => (antidiagonal n)) (fun x => f x.2.1.1 * g x.2.1.2)
  rw [← h2]
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).symm.tsum_eq]
  rw [ENNReal.tsum_prod' ]
  simp [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

lemma damagePMF_nonneg (h : ℕ → ℝ) (hh : ∀ y, 0 ≤ h y) (φ : ℝ) (y : ℕ) :
    0 ≤ damagePMF h φ y :=
  mul_nonneg (hh y) (Real.exp_pos _).le

lemma tsum_damagePMF_le (h : ℕ → ℝ) (hh : ∀ y, 0 ≤ h y) (φ : ℝ) (hφ : φ ∈ natParamSpace h) :
    ∑' y, ENNReal.ofReal (damagePMF h φ y) ≤ 1 := by
  have hsum : Summable (fun y : ℕ => h y * Real.exp (φ * y)) := hφ
  set S := ∑' y : ℕ, h y * Real.exp (φ * y) with hSdef
  have hS : 0 ≤ S := tsum_nonneg fun y => mul_nonneg (hh y) (Real.exp_pos _).le
  rcases hS.lt_or_eq with hS | hS
  · have hrw : ∀ y, damagePMF h φ y = h y * Real.exp (φ * y) / S := by
      intro y
      unfold damagePMF logPartition
      rw [Real.exp_sub, Real.exp_log hS]
      ring
    have hsm : Summable (fun y => damagePMF h φ y) := by
      simp_rw [hrw]; exact hsum.div_const S
    rw [← ENNReal.ofReal_tsum_of_nonneg (damagePMF_nonneg h hh φ) hsm]
    simp_rw [hrw]
    rw [tsum_div_const, div_self hS.ne']
    simp
  · have h0 : ∀ y, h y * Real.exp (φ * y) = 0 := by
      intro y
      have h1 := hsum.le_tsum y (fun j _ => mul_nonneg (hh j) (Real.exp_pos _).le)
      have h2 := mul_nonneg (hh y) (Real.exp_pos (φ * y)).le
      rw [← hSdef, ← hS] at h1
      linarith
    have : ∀ y, damagePMF h φ y = 0 := by
      intro y
      have hy : h y = 0 := by
        rcases mul_eq_zero.mp (h0 y) with h' | h'
        · exact h'
        · exact absurd h' (Real.exp_pos _).ne'
      simp [damagePMF, hy]
    simp [this]

lemma conv_nonneg (h : ℕ → ℝ) (hh : ∀ y, 0 ≤ h y) (φ : ℝ) : ∀ k z, 0 ≤ conv h φ k z
  | 0, z => by
      simp only [conv]; split_ifs <;> norm_num
  | k + 1, z => by
      simp only [conv]
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (conv_nonneg h hh φ k j) (damagePMF_nonneg h hh φ _)

lemma tsum_conv_le (h : ℕ → ℝ) (hh : ∀ y, 0 ≤ h y) (φ : ℝ) (hφ : φ ∈ natParamSpace h) :
    ∀ k, ∑' z, ENNReal.ofReal (conv h φ k z) ≤ 1
  | 0 => by
      rw [tsum_eq_single 0]
      · simp [conv]
      · intro b hb; simp [conv, hb]
  | k + 1 => by
      have hrw : ∀ z, ENNReal.ofReal (conv h φ (k + 1) z) =
          ∑ j ∈ Finset.range (z + 1),
            ENNReal.ofReal (conv h φ k j) * ENNReal.ofReal (damagePMF h φ (z - j)) := by
        intro z
        simp only [conv]
        rw [ENNReal.ofReal_sum_of_nonneg]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.ofReal_mul (conv_nonneg h hh φ k j)]
        · intro j _
          exact mul_nonneg (conv_nonneg h hh φ k j) (damagePMF_nonneg h hh φ _)
      simp_rw [hrw]
      rw [ennreal_cauchy (fun j => ENNReal.ofReal (conv h φ k j)) (fun i => ENNReal.ofReal (damagePMF h φ i))]
      calc _ ≤ (1 : ENNReal) * 1 :=
            mul_le_mul' (tsum_conv_le h hh φ hφ k) (tsum_damagePMF_le h hh φ hφ)
        _ = 1 := one_mul 1

lemma conjDensity_nonneg (h : ℕ → ℝ) (a b : ℝ) (hn : ConjNormalizable h a b) (φ : ℝ) :
    0 ≤ conjDensity h a b φ := by
  unfold conjDensity
  apply div_nonneg _ hn.2.le
  unfold Set.indicator
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl


lemma tsum_damagePart_le (h : ℕ → ℝ) (hh : ∀ y, 0 ≤ h y) (a b : ℝ)
    (hn : ConjNormalizable h a b) (k : ℕ) :
    ∑' z, ENNReal.ofReal (damagePart h a b k z) ≤ 1 := by
  set Z := ∫ ψ in natParamSpace h, conjKernel h a b ψ
  have hZ : 0 < Z := hn.2
  calc ∑' z, ENNReal.ofReal (damagePart h a b k z)
      ≤ ∑' z, ∫⁻ φ in natParamSpace h,
          ENNReal.ofReal (conv h φ k z * conjDensity h a b φ) := by
        apply ENNReal.tsum_le_tsum
        intro z
        exact ofReal_integral_le _ _ fun φ =>
          mul_nonneg (conv_nonneg h hh φ k z) (conjDensity_nonneg h a b hn φ)
    _ ≤ ∫⁻ φ in natParamSpace h, ∑' z,
          ENNReal.ofReal (conv h φ k z * conjDensity h a b φ) := tsum_lintegral_le _ _
    _ ≤ ∫⁻ φ in natParamSpace h, ENNReal.ofReal (conjKernel h a b φ / Z) := by
        apply lintegral_mono
        intro φ
        simp_rw [ENNReal.ofReal_mul (conv_nonneg h hh φ k _)]
        rw [ENNReal.tsum_mul_right]
        by_cases hφ : φ ∈ natParamSpace h
        · calc (∑' z, ENNReal.ofReal (conv h φ k z)) * ENNReal.ofReal (conjDensity h a b φ)
              ≤ 1 * ENNReal.ofReal (conjDensity h a b φ) := by
                gcongr; exact tsum_conv_le h hh φ hφ k
            _ = ENNReal.ofReal (conjKernel h a b φ / Z) := by
                rw [one_mul]; unfold conjDensity; rw [Set.indicator_of_mem hφ]
        · have : conjDensity h a b φ = 0 := by
            unfold conjDensity; rw [Set.indicator_of_notMem hφ, zero_div]
          rw [this]; simp
    _ = ENNReal.ofReal (∫ φ in natParamSpace h, conjKernel h a b φ / Z) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hn.1.div_const Z)]
        exact Filter.Eventually.of_forall fun φ => div_nonneg (Real.exp_pos _).le hZ.le
    _ = 1 := by
        rw [integral_div, div_self hZ.ne']; simp

lemma exp_tsum (x : ℝ) : ∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ) = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

lemma poisson_integrand_nonneg (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k : ℕ) (lam : ℝ) :
    0 ≤ Real.exp (-lam) * lam ^ k / (Nat.factorial k : ℝ) *
      ProbabilityTheory.gammaPDFReal α β lam := by
  by_cases hl : 0 ≤ lam
  · have := ProbabilityTheory.gammaPDFReal_nonneg hα hβ lam
    positivity
  · have : ProbabilityTheory.gammaPDFReal α β lam = 0 := by
      simp [ProbabilityTheory.gammaPDFReal, hl]
    rw [this, mul_zero]

lemma countPart_nonneg (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k : ℕ) : 0 ≤ countPart α β k :=
  integral_nonneg fun lam => poisson_integrand_nonneg α β hα hβ k lam

lemma tsum_countPart_le (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∑' k, ENNReal.ofReal (countPart α β k) ≤ 1 := by
  calc ∑' k, ENNReal.ofReal (countPart α β k)
      ≤ ∑' k, ∫⁻ lam, ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (Nat.factorial k : ℝ) *
          ProbabilityTheory.gammaPDFReal α β lam) := by
        apply ENNReal.tsum_le_tsum
        intro k
        exact ofReal_integral_le _ _ (poisson_integrand_nonneg α β hα hβ k)
    _ ≤ ∫⁻ lam, ∑' k, ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (Nat.factorial k : ℝ) *
          ProbabilityTheory.gammaPDFReal α β lam) := tsum_lintegral_le _ _
    _ ≤ ∫⁻ lam, ProbabilityTheory.gammaPDF α β lam := by
        apply lintegral_mono
        intro lam
        by_cases hl : 0 ≤ lam
        · have hpois : ∀ k : ℕ, 0 ≤ Real.exp (-lam) * lam ^ k / (Nat.factorial k : ℝ) := by
            intro k; positivity
          simp_rw [ENNReal.ofReal_mul (hpois _)]
          rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg hpois]
          · have : ∑' k : ℕ, Real.exp (-lam) * lam ^ k / (Nat.factorial k : ℝ) = 1 := by
              simp_rw [mul_div_assoc]
              rw [tsum_mul_left, exp_tsum, ← Real.exp_add]
              simp
            rw [this, ENNReal.ofReal_one, one_mul]
            rfl
          · simp_rw [mul_div_assoc]
            exact (Real.summable_pow_div_factorial lam).mul_left _
        · have : ProbabilityTheory.gammaPDFReal α β lam = 0 := by
            simp [ProbabilityTheory.gammaPDFReal, hl]
          simp [this]
    _ = 1 := ProbabilityTheory.lintegral_gammaPDF_eq_one hα hβ

lemma damagePart_nonneg (h : ℕ → ℝ) (hh : ∀ y, 0 ≤ h y) (a b : ℝ)
    (hn : ConjNormalizable h a b) (k z : ℕ) : 0 ≤ damagePart h a b k z :=
  integral_nonneg fun φ => mul_nonneg (conv_nonneg h hh φ k z) (conjDensity_nonneg h a b hn φ)

/-- The kernel facts: nonnegativity, summability and total mass at most one. -/
lemma kernel_facts (M : Model) (hM : M.Standing) (s : State) :
    (∀ z k, 0 ≤ M.q s z k) ∧ Summable (fun p : ℕ × ℕ => M.q s p.1 p.2) ∧
      ∑' p : ℕ × ℕ, M.q s p.1 p.2 ≤ 1 := by
  obtain ⟨x, n, t⟩ := s
  have hα : 0 < M.α0 + (n : ℝ) := by have := hM.α0_pos; positivity
  have hβ : 0 < M.β0 + (t : ℝ) := by have := hM.β0_pos; positivity
  have hn := hM.conj_normalizable x n
  have h0 : ∀ z k, 0 ≤ M.q (x, n, t) z k := by
    intro z k
    exact mul_nonneg (countPart_nonneg _ _ hα hβ k) (damagePart_nonneg _ hM.h_nonneg _ _ hn k z)
  have hE : ∑' p : ℕ × ℕ, ENNReal.ofReal (M.q (x, n, t) p.1 p.2) ≤ 1 := by
    rw [ENNReal.tsum_prod (f := fun z k => ENNReal.ofReal (M.q (x, n, t) z k)), ENNReal.tsum_comm]
    calc ∑' k, ∑' z, ENNReal.ofReal (M.q (x, n, t) z k)
        = ∑' k, ENNReal.ofReal (countPart (M.α0 + (n : ℝ)) (M.β0 + (t : ℝ)) k) *
            ∑' z, ENNReal.ofReal (damagePart M.h (M.a0 + (x : ℝ)) (M.b0 + (n : ℝ)) k z) := by
          congr 1; ext k
          rw [← ENNReal.tsum_mul_left]
          congr 1; ext z
          simp only [Model.q, predKernel]
          rw [ENNReal.ofReal_mul (countPart_nonneg _ _ hα hβ k)]
      _ ≤ ∑' k, ENNReal.ofReal (countPart (M.α0 + (n : ℝ)) (M.β0 + (t : ℝ)) k) * 1 := by
          gcongr with k
          exact tsum_damagePart_le _ hM.h_nonneg _ _ hn k
      _ ≤ 1 := by simp only [mul_one]; exact tsum_countPart_le _ _ hα hβ
  have hne : ∑' p : ℕ × ℕ, ENNReal.ofReal (M.q (x, n, t) p.1 p.2) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hE
  have hsum := ENNReal.summable_toReal hne
  have hrw : ∀ p : ℕ × ℕ, (ENNReal.ofReal (M.q (x, n, t) p.1 p.2)).toReal = M.q (x, n, t) p.1 p.2 :=
    fun p => ENNReal.toReal_ofReal (h0 p.1 p.2)
  simp_rw [hrw] at hsum
  refine ⟨h0, hsum, ?_⟩
  have := ENNReal.tsum_toReal_eq (f := fun p : ℕ × ℕ => ENNReal.ofReal (M.q (x, n, t) p.1 p.2))
    (fun _ => ENNReal.ofReal_ne_top)
  simp_rw [hrw] at this
  rw [← this]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hE)

section DP

variable (M : Model) (hM : M.Standing)
include hM

lemma Enext_summable (s : State) (W : State → ℝ) (B : ℝ) (hW0 : ∀ s, 0 ≤ W s)
    (hWB : ∀ s, W s ≤ B) :
    Summable (fun p : ℕ × ℕ => M.q s p.1 p.2 * W (s.1 + p.1, s.2.1 + p.2, s.2.2 + 1)) := by
  obtain ⟨h0, hs, -⟩ := kernel_facts M hM s
  refine Summable.of_nonneg_of_le (fun p => mul_nonneg (h0 _ _) (hW0 _))
    (fun p => mul_le_mul_of_nonneg_left (hWB _) (h0 _ _)) (hs.mul_right B)

lemma Enext_nonneg (s : State) (W : State → ℝ) (hW0 : ∀ s, 0 ≤ W s) : 0 ≤ M.Enext s W := by
  obtain ⟨h0, -, -⟩ := kernel_facts M hM s
  exact tsum_nonneg fun p => mul_nonneg (h0 _ _) (hW0 _)

lemma Enext_le (s : State) (W : State → ℝ) (B : ℝ) (hB : 0 ≤ B) (hW0 : ∀ s, 0 ≤ W s)
    (hWB : ∀ s, W s ≤ B) : M.Enext s W ≤ B := by
  obtain ⟨h0, hs, h1⟩ := kernel_facts M hM s
  unfold Model.Enext
  calc _ ≤ ∑' p : ℕ × ℕ, M.q s p.1 p.2 * B :=
        (Enext_summable M hM s W B hW0 hWB).tsum_le_tsum
          (fun p => mul_le_mul_of_nonneg_left (hWB _) (h0 _ _)) (hs.mul_right B)
    _ = (∑' p : ℕ × ℕ, M.q s p.1 p.2) * B := tsum_mul_right
    _ ≤ 1 * B := by gcongr
    _ = B := one_mul B

lemma Enext_mono (s : State) (W W' : State → ℝ) (B : ℝ) (hW0 : ∀ s, 0 ≤ W s)
    (hW'0 : ∀ s, 0 ≤ W' s) (hW'B : ∀ s, W' s ≤ B) (hWW : ∀ s, W s ≤ W' s) :
    M.Enext s W ≤ M.Enext s W' := by
  obtain ⟨h0, -, -⟩ := kernel_facts M hM s
  unfold Model.Enext
  exact (Enext_summable M hM s W B hW0 (fun s => (hWW s).trans (hW'B s))).tsum_le_tsum
    (fun p => mul_le_mul_of_nonneg_left (hWW _) (h0 _ _)) (Enext_summable M hM s W' B hW'0 hW'B)

lemma bellman_bounds (W : State → ℝ) (hW0 : ∀ s, 0 ≤ W s)
    (hWB : ∀ s, W s ≤ M.cu / (1 - M.γ)) (s : State) :
    0 ≤ M.bellman W s ∧ M.bellman W s ≤ M.cu / (1 - M.γ) := by
  have hγ0 := hM.γ_pos
  have hγ1 := hM.γ_lt_one
  have hcp := hM.cp_pos
  have hcu := hM.cp_lt_cu
  have h1γ : 0 < 1 - M.γ := by linarith
  have hB : 0 ≤ M.cu / (1 - M.γ) := div_nonneg (by linarith) h1γ.le
  have hBeq : M.cu + M.γ * (M.cu / (1 - M.γ)) = M.cu / (1 - M.γ) := by
    field_simp; ring
  have e0 := Enext_nonneg M hM s0 W hW0
  have e0' := Enext_le M hM s0 W _ hB hW0 hWB
  have e1 := Enext_nonneg M hM s W hW0
  have e1' := Enext_le M hM s W _ hB hW0 hWB
  have key : M.cu + M.γ * M.Enext s0 W ≤ M.cu / (1 - M.γ) := by
    rw [← hBeq]; gcongr
  unfold Model.bellman
  split_ifs
  · constructor
    · exact add_nonneg (by linarith) (mul_nonneg hγ0.le e0)
    · exact key
  · constructor
    · exact le_min (add_nonneg hcp.le (mul_nonneg hγ0.le e0)) (mul_nonneg hγ0.le e1)
    · exact (min_le_left _ _).trans (by linarith)

lemma valueIter_bounds : ∀ m s, 0 ≤ M.valueIter m s ∧ M.valueIter m s ≤ M.cu / (1 - M.γ)
  | 0, s => by
      have h1γ : 0 < 1 - M.γ := by linarith [hM.γ_lt_one]
      simp only [Model.valueIter]
      exact ⟨le_rfl, div_nonneg (by linarith [hM.cp_pos, hM.cp_lt_cu]) h1γ.le⟩
  | m + 1, s => by
      simp only [Model.valueIter]
      exact bellman_bounds M hM _ (fun s => (valueIter_bounds m s).1)
        (fun s => (valueIter_bounds m s).2) s

lemma bellman_mono (W W' : State → ℝ) (hW0 : ∀ s, 0 ≤ W s) (hW'0 : ∀ s, 0 ≤ W' s)
    (hW'B : ∀ s, W' s ≤ M.cu / (1 - M.γ)) (hWW : ∀ s, W s ≤ W' s) (s : State) :
    M.bellman W s ≤ M.bellman W' s := by
  have hγ0 := hM.γ_pos
  have m0 := Enext_mono M hM s0 W W' _ hW0 hW'0 hW'B hWW
  have m1 := Enext_mono M hM s W W' _ hW0 hW'0 hW'B hWW
  unfold Model.bellman
  split_ifs
  · gcongr
  · exact min_le_min (by gcongr) (by gcongr)

lemma valueIter_succ_ge : ∀ m s, M.valueIter m s ≤ M.valueIter (m + 1) s
  | 0, s => by
      simpa [Model.valueIter] using (valueIter_bounds M hM 1 s).1
  | m + 1, s => by
      show M.bellman (M.valueIter m) s ≤ M.bellman (M.valueIter (m + 1)) s
      exact bellman_mono M hM _ _ (fun s => (valueIter_bounds M hM m s).1)
        (fun s => (valueIter_bounds M hM (m + 1) s).1) (fun s => (valueIter_bounds M hM (m + 1) s).2)
        (fun s => valueIter_succ_ge m s) s

lemma valueIter_tendsto (s : State) :
    Filter.Tendsto (fun m => M.valueIter m s) Filter.atTop (nhds (M.V s)) := by
  have hmono : Monotone (fun m => M.valueIter m s) :=
    monotone_nat_of_le_succ fun m => valueIter_succ_ge M hM m s
  have hbdd : BddAbove (Set.range fun m => M.valueIter m s) :=
    ⟨M.cu / (1 - M.γ), by rintro _ ⟨m, rfl⟩; exact (valueIter_bounds M hM m s).2⟩
  have ht := tendsto_atTop_ciSup hmono hbdd
  have hV : M.V s = ⨆ m, M.valueIter m s := ht.limUnder_eq
  rw [hV]; exact ht

lemma V_bounds (s : State) : 0 ≤ M.V s ∧ M.V s ≤ M.cu / (1 - M.γ) := by
  have ht := valueIter_tendsto M hM s
  exact ⟨ge_of_tendsto' ht fun m => (valueIter_bounds M hM m s).1,
    le_of_tendsto' ht fun m => (valueIter_bounds M hM m s).2⟩

lemma Enext_tendsto (s : State) :
    Filter.Tendsto (fun m => M.Enext s (M.valueIter m)) Filter.atTop (nhds (M.Enext s M.V)) := by
  obtain ⟨h0, hs, -⟩ := kernel_facts M hM s
  have := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun (m : ℕ) (p : ℕ × ℕ) => M.q s p.1 p.2 * M.valueIter m (s.1 + p.1, s.2.1 + p.2, s.2.2 + 1))
    (g := fun p : ℕ × ℕ => M.q s p.1 p.2 * M.V (s.1 + p.1, s.2.1 + p.2, s.2.2 + 1))
    (bound := fun p => M.q s p.1 p.2 * (M.cu / (1 - M.γ)))
    (hs.mul_right _) (fun p => (valueIter_tendsto M hM _).const_mul _) ?_
  · exact this
  · refine Filter.Eventually.of_forall fun m p => ?_
    have hb := valueIter_bounds M hM m (s.1 + p.1, s.2.1 + p.2, s.2.2 + 1)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 _ _) hb.1)]
    exact mul_le_mul_of_nonneg_left hb.2 (h0 _ _)

lemma V_fixed (s : State) : M.V s = M.bellman M.V s := by
  have h1 : Filter.Tendsto (fun m => M.valueIter (m + 1) s) Filter.atTop (nhds (M.V s)) :=
    (valueIter_tendsto M hM s).comp (Filter.tendsto_add_atTop_nat 1)
  have h2 : Filter.Tendsto (fun m => M.valueIter (m + 1) s) Filter.atTop
      (nhds (M.bellman M.V s)) := by
    simp only [Model.valueIter]
    unfold Model.bellman
    have e0 := Enext_tendsto M hM s0
    have e1 := Enext_tendsto M hM s
    split_ifs
    · exact tendsto_const_nhds.add (e0.const_mul _)
    · exact (tendsto_const_nhds.add (e0.const_mul _)).min (e1.const_mul _)
  exact tendsto_nhds_unique h1 h2

end DP

end ShockCBMD10


open ShockCBMD10 in
theorem solution (M : Model) (hM : M.Standing) (x x' n t : ℕ) (hxx : x ≤ x') :
    M.V (x, n, t) ≤ M.V (x', n, t) := by
  have hmono : ∀ m, ∀ x x' n t : ℕ, x ≤ x' → M.valueIter m (x, n, t) ≤ M.valueIter m (x', n, t) := by
    intro m
    induction m with
    | zero => intro x x' n t _; simp [Model.valueIter]
    | succ m ih =>
      intro x x' n t hxx
      simp only [Model.valueIter]
      have hγ0 := hM.γ_pos
      have hcu := hM.cp_lt_cu
      have hE := ShockCBM.ControlLimit.Enext_monotone_x M hM (M.valueIter m) (M.cu / (1 - M.γ))
        (fun s => (valueIter_bounds M hM m s).1) (fun s => (valueIter_bounds M hM m s).2) ih x x' n t hxx
      unfold Model.bellman
      dsimp only
      split_ifs with h1 h2 h2
      · exact le_rfl
      · omega
      · exact (min_le_left _ _).trans (by linarith)
      · exact min_le_min le_rfl (mul_le_mul_of_nonneg_left hE hγ0.le)
  exact le_of_tendsto_of_tendsto' (valueIter_tendsto M hM _) (valueIter_tendsto M hM _)
    (fun m => hmono m x x' n t hxx)
