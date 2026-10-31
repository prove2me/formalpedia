-- Prove2me | solution 1 for ShockCBM.ControlLimit.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:39:29.001089+00:00
-- url     : https://prove2.me/submissions/eca1dfa0-4537-4f4f-8e1a-52d7036ec950

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

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


namespace ShockCBMEx
open ShockCBMD10

lemma tsum_eq_toReal (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑' n, f n = (∑' n, ENNReal.ofReal (f n)).toReal := by
  by_cases hs : Summable f
  · rw [← ENNReal.ofReal_tsum_of_nonneg hf hs, ENNReal.toReal_ofReal (tsum_nonneg hf)]
  · rw [tsum_eq_zero_of_not_summable hs]
    have : ∑' n, ENNReal.ofReal (f n) = ⊤ := by
      by_contra hne
      apply hs
      have := ENNReal.summable_toReal hne
      simpa [ENNReal.toReal_ofReal (hf _)] using this
    rw [this]; simp

lemma summable_iff_ne_top (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    Summable f ↔ ∑' n, ENNReal.ofReal (f n) ≠ ⊤ := by
  constructor
  · intro hs
    rw [← ENNReal.ofReal_tsum_of_nonneg hf hs]; exact ENNReal.ofReal_ne_top
  · intro hne
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this

variable (h : ℕ → ℝ) (hh : ∀ y, 0 ≤ h y)
include hh

lemma measurable_S : Measurable (fun φ : ℝ => ∑' y : ℕ, h y * Real.exp (φ * y)) := by
  have : (fun φ : ℝ => ∑' y : ℕ, h y * Real.exp (φ * y)) =
      fun φ => (∑' y : ℕ, ENNReal.ofReal (h y * Real.exp (φ * y))).toReal := by
    funext φ
    exact tsum_eq_toReal _ fun y => mul_nonneg (hh y) (Real.exp_pos _).le
  rw [this]
  refine Measurable.ennreal_toReal (Measurable.ennreal_tsum fun y => ?_)
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

lemma measurableSet_Θ : MeasurableSet (natParamSpace h) := by
  have : natParamSpace h = {φ | ∑' y : ℕ, ENNReal.ofReal (h y * Real.exp (φ * y)) ≠ ⊤} := by
    ext φ
    exact summable_iff_ne_top _ fun y => mul_nonneg (hh y) (Real.exp_pos _).le
  rw [this]
  refine (measurableSet_singleton ⊤).compl.preimage ?_
  refine Measurable.ennreal_tsum fun y => ?_
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

lemma measurable_damagePMF (y : ℕ) : Measurable (fun φ => damagePMF h φ y) := by
  unfold damagePMF logPartition
  have := measurable_S h hh
  fun_prop

lemma measurable_conv : ∀ k z, Measurable (fun φ => conv h φ k z)
  | 0, z => by simp only [conv]; exact measurable_const
  | k + 1, z => by
      simp only [conv]
      exact Finset.measurable_sum _ fun j _ =>
        (measurable_conv k j).mul (measurable_damagePMF h hh _)

omit hh in
lemma measurable_conjKernel (a b : ℝ) (hS : Measurable (fun φ : ℝ => ∑' y : ℕ, h y * Real.exp (φ * y))) :
    Measurable (conjKernel h a b) := by
  unfold conjKernel logPartition
  fun_prop

lemma measurable_conjDensity (a b : ℝ) : Measurable (conjDensity h a b) := by
  unfold conjDensity
  exact ((measurable_conjKernel h a b (measurable_S h hh)).indicator (measurableSet_Θ h hh)).div_const _

section Mass

/-- `S φ = ∑ h(y) e^{φ y}`. -/
lemma S_nonneg (φ : ℝ) : 0 ≤ ∑' y : ℕ, h y * Real.exp (φ * y) :=
  tsum_nonneg fun y => mul_nonneg (hh y) (Real.exp_pos _).le

omit hh in
lemma damagePMF_eq (φ : ℝ) (hS : 0 < ∑' y : ℕ, h y * Real.exp (φ * y)) (y : ℕ) :
    damagePMF h φ y = h y * Real.exp (φ * y) / ∑' y : ℕ, h y * Real.exp (φ * y) := by
  unfold damagePMF logPartition
  rw [Real.exp_sub, Real.exp_log hS]
  ring

lemma tsum_damagePMF_eq_one (φ : ℝ) (hφ : φ ∈ natParamSpace h)
    (hS : 0 < ∑' y : ℕ, h y * Real.exp (φ * y)) :
    ∑' y, ENNReal.ofReal (damagePMF h φ y) = 1 := by
  have hsum : Summable (fun y : ℕ => h y * Real.exp (φ * y)) := hφ
  have hsm : Summable (fun y => damagePMF h φ y) := by
    simp_rw [damagePMF_eq h φ hS]; exact hsum.div_const _
  rw [← ENNReal.ofReal_tsum_of_nonneg (damagePMF_nonneg h hh φ) hsm]
  simp_rw [damagePMF_eq h φ hS]
  rw [tsum_div_const, div_self hS.ne']
  simp

lemma tsum_conv_eq_one (φ : ℝ) (hφ : φ ∈ natParamSpace h)
    (hS : 0 < ∑' y : ℕ, h y * Real.exp (φ * y)) :
    ∀ k, ∑' z, ENNReal.ofReal (conv h φ k z) = 1
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
      rw [ennreal_cauchy (fun j => ENNReal.ofReal (conv h φ k j))
        (fun i => ENNReal.ofReal (damagePMF h φ i)), tsum_conv_eq_one φ hφ hS k,
        tsum_damagePMF_eq_one h hh φ hφ hS, one_mul]

lemma conv_summable (φ : ℝ) (hφ : φ ∈ natParamSpace h) (k : ℕ) :
    Summable (fun z => conv h φ k z) := by
  rw [summable_iff_ne_top _ (conv_nonneg h hh φ k)]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_conv_le h hh φ hφ k)

lemma conv_tsum_eq_one (φ : ℝ) (hφ : φ ∈ natParamSpace h)
    (hS : 0 < ∑' y : ℕ, h y * Real.exp (φ * y)) (k : ℕ) :
    ∑' z, conv h φ k z = 1 := by
  rw [tsum_eq_toReal _ (conv_nonneg h hh φ k), tsum_conv_eq_one h hh φ hφ hS k]; simp

lemma conv_le_one (φ : ℝ) (hφ : φ ∈ natParamSpace h) (k z : ℕ) : conv h φ k z ≤ 1 := by
  have h1 : ENNReal.ofReal (conv h φ k z) ≤ 1 :=
    (ENNReal.le_tsum z).trans (tsum_conv_le h hh φ hφ k)
  exact (ENNReal.ofReal_le_one).mp h1

omit hh in
lemma conv_tilt (φ φ' : ℝ) (hS : 0 < ∑' y : ℕ, h y * Real.exp (φ * y))
    (hS' : 0 < ∑' y : ℕ, h y * Real.exp (φ' * y)) :
    ∀ k z, conv h φ' k z = conv h φ k z *
      (Real.exp ((φ' - φ) * z) *
        ((∑' y : ℕ, h y * Real.exp (φ * y)) / ∑' y : ℕ, h y * Real.exp (φ' * y)) ^ k)
  | 0, z => by
      simp only [conv, pow_zero, mul_one]
      split_ifs with hz
      · subst hz; simp
      · simp
  | k + 1, z => by
      simp only [conv]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjz : j ≤ z := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [conv_tilt φ φ' hS hS' k j, damagePMF_eq h φ' hS', damagePMF_eq h φ hS]
      have hcast : ((z - j : ℕ) : ℝ) = (z : ℝ) - j := by push_cast [hjz]; ring
      rw [hcast]
      have e1 : Real.exp (φ' * ((z : ℝ) - j)) =
          Real.exp (φ * ((z : ℝ) - j)) * Real.exp ((φ' - φ) * ((z : ℝ) - j)) := by
        rw [← Real.exp_add]; ring_nf
      have e2 : Real.exp ((φ' - φ) * (z : ℝ)) =
          Real.exp ((φ' - φ) * (j : ℝ)) * Real.exp ((φ' - φ) * ((z : ℝ) - j)) := by
        rw [← Real.exp_add]; ring_nf
      rw [e1, e2]
      have h1 := hS.ne'
      have h2 := hS'.ne'
      generalize (∑' y : ℕ, h y * Real.exp (φ * y)) = S at *
      generalize (∑' y : ℕ, h y * Real.exp (φ' * y)) = S' at *
      rw [pow_succ]
      field_simp

omit hh in
lemma conv_const_of_h_zero (hz : ∀ y, h y = 0) (φ φ' : ℝ) :
    ∀ k z, conv h φ' k z = conv h φ k z
  | 0, z => rfl
  | k + 1, z => by
      simp only [conv]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [conv_const_of_h_zero hz φ φ' k j]
      simp [damagePMF, hz]

end Mass

omit hh in
lemma crossing_discrete (p v f : ℕ → ℝ) (B : ℝ) (hp : ∀ z, 0 ≤ p z) (hps : Summable p)
    (hv0 : ∀ z, 0 ≤ v z) (hpvs : Summable (fun z => p z * v z))
    (hsum : ∑' z, p z * v z = ∑' z, p z) (hv : Monotone v) (hf : Monotone f)
    (hf0 : ∀ z, 0 ≤ f z) (hfB : ∀ z, f z ≤ B) :
    ∑' z, p z * f z ≤ ∑' z, p z * v z * f z := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ z, 0 ≤ (f z - L) * (v z - 1) := by
    by_cases hA : ∃ z, 1 ≤ v z
    · refine ⟨f (Nat.find hA), fun z => ?_⟩
      by_cases hz : Nat.find hA ≤ z
      · apply mul_nonneg
        · linarith [hf hz]
        · linarith [hv hz, Nat.find_spec hA]
      · push_neg at hz
        have h1 : ¬ 1 ≤ v z := Nat.find_min hA hz
        apply mul_nonneg_of_nonpos_of_nonpos
        · linarith [hf hz.le]
        · linarith
    · push_neg at hA
      refine ⟨B, fun z => mul_nonneg_of_nonpos_of_nonpos (by linarith [hfB z]) (by linarith [hA z])⟩
  have hB : 0 ≤ B := (hf0 0).trans (hfB 0)
  have s1 : Summable (fun z => p z * f z) :=
    Summable.of_nonneg_of_le (fun z => mul_nonneg (hp z) (hf0 z))
      (fun z => mul_le_mul_of_nonneg_left (hfB z) (hp z)) (hps.mul_right B)
  have s2 : Summable (fun z => p z * v z * f z) :=
    Summable.of_nonneg_of_le (fun z => mul_nonneg (mul_nonneg (hp z) (hv0 z)) (hf0 z))
      (fun z => mul_le_mul_of_nonneg_left (hfB z) (mul_nonneg (hp z) (hv0 z))) (hpvs.mul_right B)
  have e : ∑' z, (p z * v z * f z - p z * f z - L * (p z * v z - p z)) =
      (∑' z, p z * v z * f z) - (∑' z, p z * f z) - L * ((∑' z, p z * v z) - ∑' z, p z) := by
    rw [Summable.tsum_sub (s2.sub s1) ((hpvs.sub hps).mul_left L), Summable.tsum_sub s2 s1,
      tsum_mul_left, Summable.tsum_sub hpvs hps]
  have hnn : 0 ≤ ∑' z, (p z * v z * f z - p z * f z - L * (p z * v z - p z)) := by
    apply tsum_nonneg
    intro z
    have : p z * v z * f z - p z * f z - L * (p z * v z - p z) = p z * ((f z - L) * (v z - 1)) := by
      ring
    rw [this]
    exact mul_nonneg (hp z) (hL z)
  rw [e, hsum, sub_self, mul_zero, sub_zero] at hnn
  linarith

lemma g_mono (f : ℕ → ℝ) (B : ℝ) (hf : Monotone f) (hf0 : ∀ z, 0 ≤ f z) (hfB : ∀ z, f z ≤ B)
    (k : ℕ) (φ φ' : ℝ) (hφ : φ ∈ natParamSpace h) (hφ' : φ' ∈ natParamSpace h) (hle : φ ≤ φ') :
    ∑' z, conv h φ k z * f z ≤ ∑' z, conv h φ' k z * f z := by
  rcases (S_nonneg h hh φ).lt_or_eq with hS | hS
  · have hS' : 0 < ∑' y : ℕ, h y * Real.exp (φ' * y) := by
      obtain ⟨y, hy⟩ : ∃ y, h y ≠ 0 := by
        by_contra hc
        push_neg at hc
        simp [hc] at hS
      have hpos : 0 < h y * Real.exp (φ' * y) := mul_pos (lt_of_le_of_ne (hh y) hy.symm) (Real.exp_pos _)
      have hsum' : Summable (fun y : ℕ => h y * Real.exp (φ' * y)) := hφ'
      exact hpos.trans_le (hsum'.le_tsum y fun j _ => mul_nonneg (hh j) (Real.exp_pos _).le)
    set R := (∑' y : ℕ, h y * Real.exp (φ * y)) / ∑' y : ℕ, h y * Real.exp (φ' * y) with hR
    have hR0 : 0 ≤ R := div_nonneg hS.le hS'.le
    have ht := conv_tilt h φ φ' hS hS' k
    simp_rw [ht]
    apply crossing_discrete (fun z => conv h φ k z) (fun z => Real.exp ((φ' - φ) * z) * R ^ k) f B
      (conv_nonneg h hh φ k) (conv_summable h hh φ hφ k)
      (fun z => mul_nonneg (Real.exp_pos _).le (pow_nonneg hR0 k))
    · have := conv_summable h hh φ' hφ' k
      simp_rw [ht] at this; exact this
    · have h1 := conv_tsum_eq_one h hh φ' hφ' hS' k
      simp_rw [ht] at h1
      rw [h1, conv_tsum_eq_one h hh φ hφ hS k]
    · intro a b hab
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hR0 k)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left (by exact_mod_cast hab) (by linarith)
    · exact hf
    · exact hf0
    · exact hfB
  · have hz : ∀ y, h y = 0 := by
      intro y
      have hsum : Summable (fun y : ℕ => h y * Real.exp (φ * y)) := hφ
      have h1 := hsum.le_tsum y (fun j _ => mul_nonneg (hh j) (Real.exp_pos _).le)
      rw [← hS] at h1
      have h2 := mul_nonneg (hh y) (Real.exp_pos (φ * y)).le
      have h3 : h y * Real.exp (φ * y) = 0 := le_antisymm h1 h2
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exact absurd h4 (Real.exp_pos _).ne'
    simp_rw [conv_const_of_h_zero h hz φ φ' k]
    exact le_rfl

omit hh in
lemma crossing_cont (μ : Measure ℝ) (Θ : Set ℝ) (hΘμ : ∀ᵐ φ ∂μ, φ ∈ Θ) (d w g : ℝ → ℝ) (B : ℝ)
    (hd : ∀ φ, 0 ≤ d φ) (hdi : Integrable d μ) (hdwi : Integrable (fun φ => d φ * w φ) μ)
    (hint : ∫ φ, d φ * w φ ∂μ = ∫ φ, d φ ∂μ) (hw : Monotone w) (hg : MonotoneOn g Θ)
    (hg0 : ∀ φ ∈ Θ, 0 ≤ g φ) (hgB : ∀ φ ∈ Θ, g φ ≤ B) (hgm : AEStronglyMeasurable g μ) :
    ∫ φ, d φ * g φ ∂μ ≤ ∫ φ, d φ * w φ * g φ ∂μ := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ φ ∈ Θ, 0 ≤ (g φ - L) * (w φ - 1) := by
    by_cases hA : ({φ | φ ∈ Θ ∧ 1 ≤ w φ} : Set ℝ).Nonempty
    · have hbdd : BddBelow (g '' {φ | φ ∈ Θ ∧ 1 ≤ w φ}) :=
        ⟨0, by rintro _ ⟨ψ, hψ, rfl⟩; exact hg0 ψ hψ.1⟩
      refine ⟨sInf (g '' {φ | φ ∈ Θ ∧ 1 ≤ w φ}), fun φ hφ => ?_⟩
      by_cases hw1 : 1 ≤ w φ
      · apply mul_nonneg
        · have := csInf_le hbdd ⟨φ, ⟨hφ, hw1⟩, rfl⟩
          linarith
        · linarith
      · push_neg at hw1
        apply mul_nonneg_of_nonpos_of_nonpos
        · have : g φ ≤ sInf (g '' {φ | φ ∈ Θ ∧ 1 ≤ w φ}) := by
            apply le_csInf (hA.image g)
            rintro _ ⟨ψ, hψ, rfl⟩
            apply hg hφ hψ.1
            by_contra hc
            push_neg at hc
            have := hw hc.le
            linarith [hψ.2]
          linarith
        · linarith
    · refine ⟨B, fun φ hφ => ?_⟩
      have hw1 : w φ < 1 := by
        by_contra hc
        push_neg at hc
        exact hA ⟨φ, hφ, hc⟩
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hgB φ hφ]) (by linarith)
  have hgb : ∀ᵐ φ ∂μ, ‖g φ‖ ≤ B := by
    filter_upwards [hΘμ] with φ hφ
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 φ hφ)]
    exact hgB φ hφ
  have i1 : Integrable (fun φ => d φ * g φ) μ := by
    have := hdi.bdd_mul hgm hgb
    simpa [mul_comm] using this
  have i2 : Integrable (fun φ => d φ * w φ * g φ) μ := by
    have := hdwi.bdd_mul hgm hgb
    simpa [mul_comm] using this
  have e : ∫ φ, (d φ * w φ * g φ - d φ * g φ - L * (d φ * w φ - d φ)) ∂μ =
      (∫ φ, d φ * w φ * g φ ∂μ) - (∫ φ, d φ * g φ ∂μ) -
        L * ((∫ φ, d φ * w φ ∂μ) - ∫ φ, d φ ∂μ) := by
    have j1 : Integrable (fun φ => d φ * w φ * g φ - d φ * g φ) μ := i2.sub i1
    have j2 : Integrable (fun φ => L * (d φ * w φ - d φ)) μ := (hdwi.sub hdi).const_mul L
    rw [integral_sub j1 j2, integral_sub i2 i1, integral_const_mul, integral_sub hdwi hdi]
  have hnn : 0 ≤ ∫ φ, (d φ * w φ * g φ - d φ * g φ - L * (d φ * w φ - d φ)) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hΘμ] with φ hφ
    have : d φ * w φ * g φ - d φ * g φ - L * (d φ * w φ - d φ) =
        d φ * ((g φ - L) * (w φ - 1)) := by ring
    rw [Pi.zero_apply, this]
    exact mul_nonneg (hd φ) (hL φ hφ)
  rw [e, hint, sub_self, mul_zero, sub_zero] at hnn
  linarith

lemma dens_integrable (a b : ℝ) (hn : ConjNormalizable h a b) :
    Integrable (conjDensity h a b) (volume.restrict (natParamSpace h)) := by
  unfold conjDensity
  exact (hn.1.indicator (measurableSet_Θ h hh)).div_const _

lemma dens_integral_one (a b : ℝ) (hn : ConjNormalizable h a b) :
    ∫ φ in natParamSpace h, conjDensity h a b φ = 1 := by
  unfold conjDensity
  rw [integral_div, setIntegral_indicator (measurableSet_Θ h hh), Set.inter_self,
    div_self hn.2.ne']

omit hh in
lemma dens_tilt (a a' b : ℝ) (hna : ConjNormalizable h a b) (hna' : ConjNormalizable h a' b)
    (φ : ℝ) :
    conjDensity h a' b φ = conjDensity h a b φ *
      (Real.exp ((a' - a) * φ) *
        ((∫ ψ in natParamSpace h, conjKernel h a b ψ) /
          ∫ ψ in natParamSpace h, conjKernel h a' b ψ)) := by
  have h1 := hna.2.ne'
  have h2 := hna'.2.ne'
  unfold conjDensity
  by_cases hφ : φ ∈ natParamSpace h
  · rw [Set.indicator_of_mem hφ, Set.indicator_of_mem hφ]
    have hk : conjKernel h a' b φ = conjKernel h a b φ * Real.exp ((a' - a) * φ) := by
      unfold conjKernel; rw [← Real.exp_add]; ring_nf
    rw [hk]
    generalize (∫ ψ in natParamSpace h, conjKernel h a b ψ) = Z at *
    generalize (∫ ψ in natParamSpace h, conjKernel h a' b ψ) = Z' at *
    field_simp
  · rw [Set.indicator_of_notMem hφ, Set.indicator_of_notMem hφ]; simp

lemma g_measurable (k : ℕ) (f : ℕ → ℝ) (hf0 : ∀ z, 0 ≤ f z) :
    Measurable (fun φ => ∑' z, conv h φ k z * f z) := by
  have : (fun φ => ∑' z, conv h φ k z * f z) =
      fun φ => (∑' z, ENNReal.ofReal (conv h φ k z * f z)).toReal := by
    funext φ
    exact tsum_eq_toReal _ fun z => mul_nonneg (conv_nonneg h hh φ k z) (hf0 z)
  rw [this]
  refine Measurable.ennreal_toReal (Measurable.ennreal_tsum fun z => ?_)
  exact ENNReal.measurable_ofReal.comp ((measurable_conv h hh k z).mul_const _)

lemma damagePart_summable (a b : ℝ) (hn : ConjNormalizable h a b) (k : ℕ) :
    Summable (fun z => damagePart h a b k z) := by
  rw [summable_iff_ne_top _ (damagePart_nonneg h hh a b hn k)]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_damagePart_le h hh a b hn k)

lemma lhs_eq (a b : ℝ) (hn : ConjNormalizable h a b) (k : ℕ) (f : ℕ → ℝ) (B : ℝ)
    (hf0 : ∀ z, 0 ≤ f z) (hfB : ∀ z, f z ≤ B) :
    ∑' z, damagePart h a b k z * f z =
      ∫ φ in natParamSpace h, conjDensity h a b φ * ∑' z, conv h φ k z * f z := by
  have hΘ := measurableSet_Θ h hh
  have hint : ∀ z, Integrable (fun φ => conv h φ k z * conjDensity h a b φ * f z)
      (volume.restrict (natParamSpace h)) := by
    intro z
    refine Integrable.mul_const ?_ _
    refine (dens_integrable h hh a b hn).bdd_mul (c := 1)
      (measurable_conv h hh k z).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hΘ] with φ hφ
    rw [Real.norm_eq_abs, abs_of_nonneg (conv_nonneg h hh φ k z)]
    exact conv_le_one h hh φ hφ k z
  have hnn : ∀ z φ, 0 ≤ conv h φ k z * conjDensity h a b φ * f z := fun z φ =>
    mul_nonneg (mul_nonneg (conv_nonneg h hh φ k z) (conjDensity_nonneg h a b hn φ)) (hf0 z)
  have hB : 0 ≤ B := (hf0 0).trans (hfB 0)
  calc ∑' z, damagePart h a b k z * f z
      = ∑' z, ∫ φ in natParamSpace h, conv h φ k z * conjDensity h a b φ * f z := by
        congr 1; ext z
        unfold damagePart
        rw [integral_mul_const]
    _ = ∫ φ in natParamSpace h, ∑' z, conv h φ k z * conjDensity h a b φ * f z := by
        apply integral_tsum_of_summable_integral_norm hint
        have : ∀ z, ∫ φ in natParamSpace h, ‖conv h φ k z * conjDensity h a b φ * f z‖ =
            damagePart h a b k z * f z := by
          intro z
          simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnn z _)]
          unfold damagePart
          rw [integral_mul_const]
        simp_rw [this]
        exact Summable.of_nonneg_of_le
          (fun z => mul_nonneg (damagePart_nonneg h hh a b hn k z) (hf0 z))
          (fun z => mul_le_mul_of_nonneg_left (hfB z) (damagePart_nonneg h hh a b hn k z))
          ((damagePart_summable h hh a b hn k).mul_right B)
    _ = ∫ φ in natParamSpace h, conjDensity h a b φ * ∑' z, conv h φ k z * f z := by
        congr 1; ext φ
        rw [← tsum_mul_left]
        congr 1; ext z
        ring

lemma key_L (a a' b : ℝ) (hna : ConjNormalizable h a b) (hna' : ConjNormalizable h a' b)
    (haa : a ≤ a') (k : ℕ) (f : ℕ → ℝ) (B : ℝ) (hf : Monotone f) (hf0 : ∀ z, 0 ≤ f z)
    (hfB : ∀ z, f z ≤ B) :
    ∑' z, damagePart h a b k z * f z ≤ ∑' z, damagePart h a' b k z * f z := by
  have hΘ := measurableSet_Θ h hh
  rw [lhs_eq h hh a b hna k f B hf0 hfB, lhs_eq h hh a' b hna' k f B hf0 hfB]
  set w : ℝ → ℝ := fun φ => Real.exp ((a' - a) * φ) *
      ((∫ ψ in natParamSpace h, conjKernel h a b ψ) /
        ∫ ψ in natParamSpace h, conjKernel h a' b ψ) with hw
  have ht : ∀ φ, conjDensity h a' b φ = conjDensity h a b φ * w φ :=
    dens_tilt h a a' b hna hna'
  simp_rw [ht]
  have hB : 0 ≤ B := (hf0 0).trans (hfB 0)
  apply crossing_cont _ (natParamSpace h) (ae_restrict_mem hΘ) (conjDensity h a b) w
    (fun φ => ∑' z, conv h φ k z * f z) B (conjDensity_nonneg h a b hna)
    (dens_integrable h hh a b hna)
  · have := dens_integrable h hh a' b hna'
    rwa [show conjDensity h a' b = fun φ => conjDensity h a b φ * w φ from funext ht] at this
  · have h1 := dens_integral_one h hh a' b hna'
    simp_rw [ht] at h1
    rw [h1, dens_integral_one h hh a b hna]
  · intro u v huv
    simp only [hw]
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hna.2.le hna'.2.le)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huv (by linarith))
  · intro u hu v hv huv
    exact g_mono h hh f B hf hf0 hfB k u v hu hv huv
  · intro φ _
    exact tsum_nonneg fun z => mul_nonneg (conv_nonneg h hh φ k z) (hf0 z)
  · intro φ hφ
    have hs := conv_summable h hh φ hφ k
    calc ∑' z, conv h φ k z * f z ≤ ∑' z, conv h φ k z * B :=
          Summable.tsum_le_tsum (fun z => mul_le_mul_of_nonneg_left (hfB z) (conv_nonneg h hh φ k z))
            (Summable.of_nonneg_of_le (fun z => mul_nonneg (conv_nonneg h hh φ k z) (hf0 z))
              (fun z => mul_le_mul_of_nonneg_left (hfB z) (conv_nonneg h hh φ k z)) (hs.mul_right B))
            (hs.mul_right B)
      _ = (∑' z, conv h φ k z) * B := tsum_mul_right
      _ ≤ 1 * B := by
          gcongr
          rw [tsum_eq_toReal _ (conv_nonneg h hh φ k)]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one
            (by simpa using tsum_conv_le h hh φ hφ k)
      _ = B := one_mul B
  · exact (g_measurable h hh k f hf0).aestronglyMeasurable

end ShockCBMEx


namespace ShockCBMP1
open ShockCBMD10 ShockCBMEx

lemma integral_gammaPDFReal_eq_one (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∫ x, ProbabilityTheory.gammaPDFReal a r x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (ProbabilityTheory.gammaPDFReal_nonneg ha hr))
    (ProbabilityTheory.measurable_gammaPDFReal a r).aestronglyMeasurable]
  have : ∫⁻ x, ENNReal.ofReal (ProbabilityTheory.gammaPDFReal a r x) = 1 :=
    ProbabilityTheory.lintegral_gammaPDF_eq_one ha hr
  rw [this]; simp

lemma gamma_part (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k : ℕ) (lam : ℝ) :
    Real.exp (-lam) * lam ^ k / (Nat.factorial k : ℝ) * ProbabilityTheory.gammaPDFReal α β lam =
      (β ^ α * Real.Gamma (α + k) /
        ((Nat.factorial k : ℝ) * Real.Gamma α * (β + 1) ^ (α + k))) *
        ProbabilityTheory.gammaPDFReal (α + k) (β + 1) lam := by
  have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  have hG' : 0 < Real.Gamma (α + k) := Real.Gamma_pos_of_pos (by positivity)
  have hk : (0 : ℝ) < Nat.factorial k := by exact_mod_cast Nat.factorial_pos k
  have hb1 : 0 < β + 1 := by linarith
  unfold ProbabilityTheory.gammaPDFReal
  by_cases hl : 0 ≤ lam
  · rw [if_pos hl, if_pos hl]
    rcases hl.lt_or_eq with hl | hl
    · have e1 : lam ^ (α + k - 1) = lam ^ k * lam ^ (α - 1) := by
        rw [show α + (k : ℝ) - 1 = (k : ℝ) + (α - 1) by ring, Real.rpow_add hl, Real.rpow_natCast]
      have e2 : Real.exp (-((β + 1) * lam)) = Real.exp (-lam) * Real.exp (-(β * lam)) := by
        rw [← Real.exp_add]; ring_nf
      rw [e1, e2]
      have : (β + 1) ^ (α + k) ≠ 0 := (Real.rpow_pos_of_pos hb1 _).ne'
      field_simp
    · subst hl
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        simp only [pow_zero, Nat.cast_zero, add_zero, Nat.factorial_zero, Nat.cast_one]
        have : (β + 1) ^ α ≠ 0 := (Real.rpow_pos_of_pos hb1 _).ne'
        have hβα : β ^ α ≠ 0 := (Real.rpow_pos_of_pos hβ _).ne'
        by_cases hα1 : α - 1 = 0
        · rw [hα1, Real.rpow_zero]
          field_simp
          try simp
        · rw [Real.zero_rpow hα1]; simp
      · have h1 : (0 : ℝ) ^ k = 0 := zero_pow (by omega)
        have h2 : α + (k : ℝ) - 1 ≠ 0 := by
          have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
          linarith
        rw [h1, Real.zero_rpow h2]; simp
  · rw [if_neg hl, if_neg hl]; simp

end ShockCBMP1

open ShockCBMD10 ShockCBMEx ShockCBMP1 in
theorem solution (h : ℕ → ℝ) (hh : ∀ y, 0 ≤ h y) (α β a b : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ha : 0 < a) (hb : 0 < b) (hab : ConjNormalizable h a b) (k : ℕ) (y : Fin k → ℕ)
    (hy : ∀ i, 0 < h (y i)) (lam φ : ℝ) :
    posterior h α β a b k y lam φ =
      ProbabilityTheory.gammaPDFReal (α + k) (β + 1) lam *
        conjDensity h (a + ∑ i, (y i : ℝ)) (b + k) φ := by
  have hΘ := measurableSet_Θ h hh
  set Sy : ℝ := ∑ i, (y i : ℝ) with hSy
  set Z := ∫ ψ in natParamSpace h, conjKernel h a b ψ with hZ
  set Z' := ∫ ψ in natParamSpace h, conjKernel h (a + Sy) (b + k) ψ with hZ'
  set P := ∏ i, h (y i) with hP
  have hZpos : 0 < Z := hab.2
  have hPpos : 0 < P := Finset.prod_pos fun i _ => hy i
  -- the tilted kernel
  have hKt : ∀ ψ, conjKernel h (a + Sy) (b + k) ψ =
      conjKernel h a b ψ * ∏ i, Real.exp (ψ * (y i : ℝ) - logPartition h ψ) := by
    intro ψ
    unfold conjKernel
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [hSy]
    ring
  have hfac_le : ∀ ψ ∈ natParamSpace h, ∀ i,
      Real.exp (ψ * (y i : ℝ) - logPartition h ψ) ≤ 1 / h (y i) := by
    intro ψ hψ i
    have hsum : Summable (fun y : ℕ => h y * Real.exp (ψ * y)) := hψ
    have hle := hsum.le_tsum (y i) (fun j _ => mul_nonneg (hh j) (Real.exp_pos _).le)
    have hS : 0 < ∑' y : ℕ, h y * Real.exp (ψ * y) :=
      (mul_pos (hy i) (Real.exp_pos _)).trans_le hle
    unfold logPartition
    rw [Real.exp_sub, Real.exp_log hS, div_le_div_iff₀ hS (hy i)]
    linarith
  have hKm : ∀ c d : ℝ, Measurable (conjKernel h c d) := fun c d =>
    measurable_conjKernel h c d (measurable_S h hh)
  have hK'int : IntegrableOn (conjKernel h (a + Sy) (b + k)) (natParamSpace h) := by
    refine Integrable.mono' (hab.1.div_const P) (hKm _ _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hΘ] with ψ hψ
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold conjKernel; exact (Real.exp_pos _).le), hKt ψ,
      div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    rw [hP, ← Finset.prod_inv_distrib]
    apply Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
    intro i _
    rw [← one_div]; exact hfac_le ψ hψ i
  have hZ'pos : 0 < Z' := by
    have hvol : 0 < volume (natParamSpace h) := by
      rw [pos_iff_ne_zero]
      intro h0
      have : volume.restrict (natParamSpace h) = 0 := Measure.restrict_eq_zero.mpr h0
      rw [hZ, this, integral_zero_measure] at hZpos
      exact lt_irrefl _ hZpos
    rw [hZ', integral_pos_iff_support_of_nonneg (f := conjKernel h (a + Sy) (b + k))
      (fun ψ => by unfold conjKernel; exact (Real.exp_pos _).le) hK'int]
    have : Function.support (conjKernel h (a + Sy) (b + k)) = Set.univ := by
      ext ψ; simp [Function.mem_support, conjKernel, (Real.exp_pos _).ne']
    rw [this, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hvol
  -- factorisation of likelihood times prior
  set cA := β ^ α * Real.Gamma (α + k) / ((Nat.factorial k : ℝ) * Real.Gamma α * (β + 1) ^ (α + k))
  set cB := P * Z' / Z
  have hcA : 0 < cA := by
    have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
    have hG' : 0 < Real.Gamma (α + k) := Real.Gamma_pos_of_pos (by positivity)
    have hk : (0 : ℝ) < Nat.factorial k := by exact_mod_cast Nat.factorial_pos k
    have : 0 < (β + 1) ^ (α + k) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hcB : 0 < cB := by positivity
  have hB : ∀ ψ, (∏ i, h (y i) * Real.exp (ψ * (y i : ℝ) - logPartition h ψ)) * conjDensity h a b ψ =
      cB * conjDensity h (a + Sy) (b + k) ψ := by
    intro ψ
    unfold conjDensity
    by_cases hψ : ψ ∈ natParamSpace h
    · rw [Set.indicator_of_mem hψ, Set.indicator_of_mem hψ, Finset.prod_mul_distrib, hKt ψ]
      rw [← hZ, ← hZ']
      simp only [cB]
      field_simp
      rw [hP]; ring
    · rw [Set.indicator_of_notMem hψ, Set.indicator_of_notMem hψ]; simp
  have hLP : ∀ p : ℝ × ℝ, likelihood h k y p.1 p.2 * jointPrior h α β a b p.1 p.2 =
      (cA * ProbabilityTheory.gammaPDFReal (α + k) (β + 1) p.1) *
        (cB * conjDensity h (a + Sy) (b + k) p.2) := by
    intro p
    rw [← gamma_part α β hα hβ k p.1, ← hB p.2]
    unfold likelihood jointPrior
    ring
  have hI : ∫ p : ℝ × ℝ, likelihood h k y p.1 p.2 * jointPrior h α β a b p.1 p.2 = cA * cB := by
    simp_rw [hLP]
    rw [Measure.volume_eq_prod, integral_prod_mul (fun l => cA * ProbabilityTheory.gammaPDFReal (α + k) (β + 1) l)
      (fun ψ => cB * conjDensity h (a + Sy) (b + k) ψ)]
    rw [integral_const_mul, integral_const_mul, integral_gammaPDFReal_eq_one _ _ (by positivity) (by linarith)]
    have : ∫ ψ, conjDensity h (a + Sy) (b + k) ψ = 1 := by
      unfold conjDensity
      rw [integral_div, integral_indicator hΘ, ← hZ', div_self hZ'pos.ne']
    rw [this]; ring
  unfold posterior
  rw [hI, show likelihood h k y lam φ * jointPrior h α β a b lam φ =
    likelihood h k y (lam, φ).1 (lam, φ).2 * jointPrior h α β a b (lam, φ).1 (lam, φ).2 from rfl, hLP]
  field_simp
