-- Prove2me | solution 1 for ResolvingNRM.IRT.regret_decomposition
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:08:55.550473+00:00
-- url     : https://prove2.me/submissions/402efa36-20d9-417c-a2bb-ad47cd08db6b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model
import Theorems.Thm_ResolvingNRM_IRT_prop1_one_resolve
import Theorems.Thm_ResolvingNRM_IRT_spa_dlp_gap_sqrt
import Theorems.Thm_ResolvingNRM_IRT_hindsight_le_dlp

open RLPBidPrice.Unbiased Matrix ResolvingNRM.IRT Finset

/-! ### Poisson partial sums -/

lemma irt_rd_pmf_nonneg (μ : ℝ) (k : ℕ) : 0 ≤ poissonPMF μ k := by
  unfold poissonPMF
  have : 0 ≤ max μ 0 := le_max_right _ _
  positivity

lemma irt_rd_pmf_sum_le (μ : ℝ) (N : ℕ) : ∑ i ∈ range N, poissonPMF μ i ≤ 1 := by
  unfold poissonPMF
  have h0 : 0 ≤ max μ 0 := le_max_right _ _
  have h := Real.sum_le_exp_of_nonneg h0 N
  have : ∑ i ∈ range N, Real.exp (-max μ 0) * max μ 0 ^ i / (i.factorial : ℝ) =
      Real.exp (-max μ 0) * ∑ i ∈ range N, max μ 0 ^ i / (i.factorial : ℝ) := by
    rw [mul_sum]; congr 1; ext i; ring
  rw [this]
  calc Real.exp (-max μ 0) * ∑ i ∈ range N, max μ 0 ^ i / (i.factorial : ℝ)
      ≤ Real.exp (-max μ 0) * Real.exp (max μ 0) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

lemma irt_rd_pmf_mean_le (μ : ℝ) (N : ℕ) :
    ∑ i ∈ range N, poissonPMF μ i * (i : ℝ) ≤ max μ 0 := by
  have hμ : 0 ≤ max μ 0 := le_max_right _ _
  rcases N with _ | N
  · simpa using hμ
  rw [sum_range_succ']
  have hshift : ∀ i ∈ range N, poissonPMF μ (i + 1) * ((i + 1 : ℕ) : ℝ) =
      max μ 0 * poissonPMF μ i := by
    intro i _
    unfold poissonPMF
    rw [Nat.factorial_succ]
    push_cast
    have : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [sum_congr rfl hshift, ← mul_sum]
  simp only [CharP.cast_eq_zero, mul_zero, add_zero]
  calc max μ 0 * ∑ i ∈ range N, poissonPMF μ i ≤ max μ 0 * 1 :=
        mul_le_mul_of_nonneg_left (irt_rd_pmf_sum_le μ N) hμ
    _ = max μ 0 := mul_one _

lemma irt_rd_pmf_summable (μ : ℝ) : Summable (fun N => poissonPMF μ N) :=
  summable_of_sum_range_le (fun N => irt_rd_pmf_nonneg μ N) (irt_rd_pmf_sum_le μ)

lemma irt_rd_pmf_tsum_le (μ : ℝ) : ∑' N, poissonPMF μ N ≤ 1 :=
  Real.tsum_le_of_sum_range_le (fun N => irt_rd_pmf_nonneg μ N) (irt_rd_pmf_sum_le μ)

lemma irt_rd_pmf_lin_summable (μ R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    Summable (fun N : ℕ => poissonPMF μ N * ((N : ℝ) * R + D)) := by
  refine summable_of_sum_range_le (c := max μ 0 * R + D)
    (fun N => mul_nonneg (irt_rd_pmf_nonneg μ N) (by positivity)) (fun N => ?_)
  have e : ∑ i ∈ range N, poissonPMF μ i * ((i : ℝ) * R + D) =
      R * ∑ i ∈ range N, poissonPMF μ i * (i : ℝ) + D * ∑ i ∈ range N, poissonPMF μ i := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; congr 1; ext i; ring
  rw [e]
  have h1 := irt_rd_pmf_mean_le μ N
  have h2 := irt_rd_pmf_sum_le μ N
  nlinarith

/-! ### One run of a probabilistic allocation -/

lemma irt_rd_runWindow_bounds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (L : List (Fin n × Bool)) :
    ∀ c : Fin m → ℝ, 0 ≤ c →
      0 ≤ (runWindow A r L c).1 ∧ (runWindow A r L c).1 ≤ L.length * ∑ j, r j ∧
        0 ≤ (runWindow A r L c).2 := by
  induction L with
  | nil => intro c hc; simp [runWindow, hc]
  | cons a rest ih =>
    intro c hc
    obtain ⟨j, b⟩ := a
    have hrj : r j ≤ ∑ j', r j' :=
      single_le_sum (f := r) (fun j' _ => hr j') (mem_univ j)
    by_cases h : b = true ∧ ∀ l, A l j ≤ c l
    · have hc' : 0 ≤ (fun l => c l - A l j) := fun l => by
        have := h.2 l; simp only [Pi.zero_apply]; linarith
      obtain ⟨h1, h2, h3⟩ := ih _ hc'
      simp only [runWindow, if_pos h, List.length_cons]
      refine ⟨by linarith [hr j], ?_, h3⟩
      push_cast
      nlinarith
    · obtain ⟨h1, h2, h3⟩ := ih c hc
      simp only [runWindow, if_neg h, List.length_cons]
      refine ⟨h1, ?_, h3⟩
      push_cast
      have : 0 ≤ ∑ j', r j' := sum_nonneg fun j' _ => hr j'
      nlinarith

/-! ### The weights of a window -/

lemma irt_rd_wt_nonneg {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (N : ℕ) (cls : Fin N → Fin n)
    (coin : Fin N → Bool) :
    0 ≤ ∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i)) := by
  apply prod_nonneg
  intro i _
  have hΛ : 0 ≤ ∑ j, lam j := sum_nonneg fun j _ => (hlam j).le
  have h1 : 0 ≤ lam (cls i) / ∑ j, lam j := div_nonneg (hlam _).le hΛ
  have h2 : 0 ≤ (if coin i then p (cls i) else 1 - p (cls i)) := by
    split_ifs
    · exact hp0 _
    · linarith [hp1 (cls i)]
  exact mul_nonneg h1 h2

lemma irt_rd_wt_sum_le {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (N : ℕ) :
    ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
      ∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i)) ≤ 1 := by
  have hcoin : ∀ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
      ∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i)) =
        ∏ i, lam (cls i) / ∑ j, lam j := by
    intro cls
    rw [← Fintype.prod_sum (fun i (b : Bool) => (lam (cls i) / ∑ j, lam j) *
      (if b = true then p (cls i) else 1 - p (cls i)))]
    congr 1; ext i
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    ring
  rw [Fintype.sum_congr _ _ hcoin]
  rw [← Fintype.prod_sum (fun _ j => lam j / ∑ j', lam j')]
  rw [prod_const]
  have hΛ : 0 ≤ ∑ j, lam j := sum_nonneg fun j _ => (hlam j).le
  have hs : ∑ j, lam j / ∑ j', lam j' ≤ 1 := by
    rw [← sum_div]
    rcases eq_or_lt_of_le hΛ with h | h
    · rw [← h]; simp
    · rw [div_self h.ne']
  have hs0 : 0 ≤ ∑ j, lam j / ∑ j', lam j' :=
    sum_nonneg fun j _ => div_nonneg (hlam j).le hΛ
  exact pow_le_one₀ hs0 hs

/-! ### Window values with bounded continuations -/

lemma irt_rd_inner_abs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) (c : Fin m → ℝ) (hc : 0 ≤ c) (W : (Fin m → ℝ) → ℝ) (D : ℝ)
    (hW : ∀ c', 0 ≤ c' → |W c'| ≤ D) (N : ℕ) :
    |∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
      (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
        ((runWindow A r (List.ofFn fun i => (cls i, coin i)) c).1 +
          W (runWindow A r (List.ofFn fun i => (cls i, coin i)) c).2)| ≤
      (N : ℝ) * ∑ j, r j + D := by
  have hD : 0 ≤ D := le_trans (abs_nonneg _) (hW 0 le_rfl)
  have hR : 0 ≤ ∑ j, r j := sum_nonneg fun j _ => hr j
  refine le_trans (abs_sum_le_sum_abs _ _) ?_
  refine le_trans (sum_le_sum fun cls _ => abs_sum_le_sum_abs _ _) ?_
  have hpt : ∀ cls : Fin N → Fin n, ∀ coin : Fin N → Bool,
      |(∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
        ((runWindow A r (List.ofFn fun i => (cls i, coin i)) c).1 +
          W (runWindow A r (List.ofFn fun i => (cls i, coin i)) c).2)| ≤
        (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
          ((N : ℝ) * ∑ j, r j + D) := by
    intro cls coin
    have hw := irt_rd_wt_nonneg lam p hlam hp0 hp1 N cls coin
    obtain ⟨h1, h2, h3⟩ := irt_rd_runWindow_bounds A r hr
      (List.ofFn fun i => (cls i, coin i)) c hc
    rw [List.length_ofFn] at h2
    have h4 := hW _ h3
    rw [abs_mul, abs_of_nonneg hw]
    apply mul_le_mul_of_nonneg_left _ hw
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_of_nonneg h1]
    linarith
  refine le_trans (sum_le_sum fun cls _ => sum_le_sum fun coin _ => hpt cls coin) ?_
  simp_rw [← sum_mul]
  have := irt_rd_wt_sum_le lam p hlam N
  have h0 : 0 ≤ (N : ℝ) * ∑ j, r j + D := by positivity
  nlinarith

lemma irt_rd_window_summable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (ℓ : ℝ) (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) (c : Fin m → ℝ) (hc : 0 ≤ c) (W : (Fin m → ℝ) → ℝ) (D : ℝ)
    (hW : ∀ c', 0 ≤ c' → |W c'| ≤ D) :
    Summable (fun N : ℕ => poissonPMF ((∑ j, lam j) * ℓ) N *
      ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
        (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
          ((runWindow A r (List.ofFn fun i => (cls i, coin i)) c).1 +
            W (runWindow A r (List.ofFn fun i => (cls i, coin i)) c).2)) := by
  have hD : 0 ≤ D := le_trans (abs_nonneg _) (hW 0 le_rfl)
  have hR : 0 ≤ ∑ j, r j := sum_nonneg fun j _ => hr j
  refine Summable.of_norm_bounded (irt_rd_pmf_lin_summable ((∑ j, lam j) * ℓ) _ D hR hD) ?_
  intro N
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (irt_rd_pmf_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left
    (irt_rd_inner_abs A r lam hlam hr p hp0 hp1 c hc W D hW N) (irt_rd_pmf_nonneg _ _)

lemma irt_rd_window_abs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (ℓ : ℝ) (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) (c : Fin m → ℝ) (hc : 0 ≤ c) (W : (Fin m → ℝ) → ℝ) (D : ℝ)
    (hW : ∀ c', 0 ≤ c' → |W c'| ≤ D) :
    |windowValue A r lam ℓ p c W| ≤ max ((∑ j, lam j) * ℓ) 0 * ∑ j, r j + D := by
  have hD : 0 ≤ D := le_trans (abs_nonneg _) (hW 0 le_rfl)
  have hR : 0 ≤ ∑ j, r j := sum_nonneg fun j _ => hr j
  set μ := (∑ j, lam j) * ℓ
  unfold windowValue
  refine le_trans (norm_tsum_le_tsum_norm
    (irt_rd_window_summable A r lam hlam hr ℓ p hp0 hp1 c hc W D hW).norm) ?_
  refine le_trans (Summable.tsum_le_tsum (g := fun N : ℕ => poissonPMF μ N * ((N : ℝ) *
      ∑ j, r j + D)) (fun N => ?_)
    (irt_rd_window_summable A r lam hlam hr ℓ p hp0 hp1 c hc W D hW).norm
    (irt_rd_pmf_lin_summable μ _ D hR hD)) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (irt_rd_pmf_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left
      (irt_rd_inner_abs A r lam hlam hr p hp0 hp1 c hc W D hW N) (irt_rd_pmf_nonneg _ _)
  · refine Real.tsum_le_of_sum_range_le
      (fun N => mul_nonneg (irt_rd_pmf_nonneg μ N) (by positivity)) (fun N => ?_)
    have e : ∑ i ∈ range N, poissonPMF μ i * ((i : ℝ) * ∑ j, r j + D) =
        (∑ j, r j) * ∑ i ∈ range N, poissonPMF μ i * (i : ℝ) +
          D * ∑ i ∈ range N, poissonPMF μ i := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]; congr 1; ext i; ring
    rw [e]
    have h1 := irt_rd_pmf_mean_le μ N
    have h2 := irt_rd_pmf_sum_le μ N
    nlinarith

lemma irt_rd_window_diff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (ℓ : ℝ) (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) (c : Fin m → ℝ) (hc : 0 ≤ c) (W₁ W₂ : (Fin m → ℝ) → ℝ) (D₁ D₂ B : ℝ)
    (hW₁ : ∀ c', 0 ≤ c' → |W₁ c'| ≤ D₁) (hW₂ : ∀ c', 0 ≤ c' → |W₂ c'| ≤ D₂) (hB : 0 ≤ B)
    (hdiff : ∀ c', 0 ≤ c' → W₁ c' - W₂ c' ≤ B) :
    windowValue A r lam ℓ p c W₁ - windowValue A r lam ℓ p c W₂ ≤ B := by
  set μ := (∑ j, lam j) * ℓ
  unfold windowValue
  rw [← Summable.tsum_sub (irt_rd_window_summable A r lam hlam hr ℓ p hp0 hp1 c hc W₁ D₁ hW₁)
    (irt_rd_window_summable A r lam hlam hr ℓ p hp0 hp1 c hc W₂ D₂ hW₂)]
  have hpt : ∀ N : ℕ,
      poissonPMF μ N * ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
        (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
          ((runWindow A r (List.ofFn fun i => (cls i, coin i)) c).1 +
            W₁ (runWindow A r (List.ofFn fun i => (cls i, coin i)) c).2) -
      poissonPMF μ N * ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
        (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
          ((runWindow A r (List.ofFn fun i => (cls i, coin i)) c).1 +
            W₂ (runWindow A r (List.ofFn fun i => (cls i, coin i)) c).2) ≤
      poissonPMF μ N * B := by
    intro N
    rw [← mul_sub, ← sum_sub_distrib]
    apply mul_le_mul_of_nonneg_left _ (irt_rd_pmf_nonneg _ _)
    simp_rw [← sum_sub_distrib, ← mul_sub]
    have hpt2 : ∀ cls : Fin N → Fin n, ∀ coin : Fin N → Bool,
        (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
          ((runWindow A r (List.ofFn fun i => (cls i, coin i)) c).1 +
              W₁ (runWindow A r (List.ofFn fun i => (cls i, coin i)) c).2 -
            ((runWindow A r (List.ofFn fun i => (cls i, coin i)) c).1 +
              W₂ (runWindow A r (List.ofFn fun i => (cls i, coin i)) c).2)) ≤
        (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) * B := by
      intro cls coin
      apply mul_le_mul_of_nonneg_left _ (irt_rd_wt_nonneg lam p hlam hp0 hp1 N cls coin)
      have := hdiff _ (irt_rd_runWindow_bounds A r hr
        (List.ofFn fun i => (cls i, coin i)) c hc).2.2
      linarith
    refine le_trans (sum_le_sum fun cls _ => sum_le_sum fun coin _ => hpt2 cls coin) ?_
    simp_rw [← sum_mul]
    have := irt_rd_wt_sum_le lam p hlam N
    nlinarith
  calc _ ≤ ∑' N : ℕ, poissonPMF μ N * B :=
        Summable.tsum_le_tsum hpt
          ((irt_rd_window_summable A r lam hlam hr ℓ p hp0 hp1 c hc W₁ D₁ hW₁).sub
            (irt_rd_window_summable A r lam hlam hr ℓ p hp0 hp1 c hc W₂ D₂ hW₂))
          ((irt_rd_pmf_summable μ).mul_right B)
    _ = (∑' N : ℕ, poissonPMF μ N) * B := tsum_mul_right
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right (irt_rd_pmf_tsum_le μ) hB
    _ = B := one_mul B

/-! ### Acceptance probabilities lie in `[0, 1]` -/

lemma irt_rd_plain_mem {n : ℕ} (lam x : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (hx0 : 0 ≤ x)
    (hx1 : x ≤ lam) (j : Fin n) : 0 ≤ plainProbs lam x j ∧ plainProbs lam x j ≤ 1 := by
  unfold plainProbs
  exact ⟨div_nonneg (hx0 j) (hlam j).le, (div_le_one (hlam j)).mpr (hx1 j)⟩

lemma irt_rd_thr_mem {n : ℕ} (lam : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (hx0 : 0 ≤ x) (hx1 : x ≤ lam) (j : Fin n) :
    0 ≤ thresholdProbs lam τ x j ∧ thresholdProbs lam τ x j ≤ 1 := by
  unfold thresholdProbs
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨div_nonneg (hx0 j) (hlam j).le, (div_le_one (hlam j)).mpr (hx1 j)⟩

/-! ### Boundedness of the value functions -/

lemma irt_rd_piValue_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (x : Fin m → ℝ) (hx : 0 ≤ x) (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) :
    0 ≤ piValue A r x y₀ := by
  unfold piValue
  apply le_csSup
  · refine ⟨r ⬝ᵥ y₀, ?_⟩
    rintro v ⟨y', -, -, hy', rfl⟩
    unfold dotProduct
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy' j) (hr j)
  · exact ⟨0, by simpa using hx, le_rfl, hy₀, by simp⟩

lemma irt_rd_piValue_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (x : Fin m → ℝ) (hx : 0 ≤ x) (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) :
    piValue A r x y₀ ≤ r ⬝ᵥ y₀ := by
  unfold piValue
  apply csSup_le
  · exact ⟨0, 0, by simpa using hx, le_rfl, hy₀, by simp⟩
  · rintro v ⟨y', -, -, hy', rfl⟩
    unfold dotProduct
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy' j) (hr j)

lemma irt_rd_ho_abs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) (τ : ℝ) (hτ : 0 < τ) :
    ∀ c : Fin m → ℝ, 0 ≤ c → |hindsightValue A r lam τ c| ≤ τ * (r ⬝ᵥ lam) := by
  intro c hc
  have h0 : 0 ≤ hindsightValue A r lam τ c := by
    unfold hindsightValue
    exact tsum_nonneg fun k => mul_nonneg (prod_nonneg fun j _ => irt_rd_pmf_nonneg _ _)
      (irt_rd_piValue_nonneg A r hr c hc _ fun j => Nat.cast_nonneg _)
  have h1 := hindsight_le_dlp A r lam hlam hr hA τ hτ c hc
  have h2 : dlpValue A r lam τ c ≤ τ * (r ⬝ᵥ lam) := by
    unfold dlpValue
    exact mul_le_mul_of_nonneg_left
      (irt_rd_piValue_le A r hr _ (fun l => div_nonneg (hc l) hτ.le) lam
        (fun j => (hlam j).le)) hτ.le
  rw [abs_of_nonneg h0]
  linarith

lemma irt_rd_tau_nonneg (T : ℝ) (hT : 1 ≤ T) (u : ℕ) : 0 ≤ tau T u :=
  Real.rpow_nonneg (by linarith) _

lemma irt_rd_irt_abs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : IsDLPSelector A r lam sel) (T : ℝ) (hT : 1 ≤ T) :
    ∀ d u : ℕ, ∃ D : ℝ, ∀ c : Fin m → ℝ, 0 ≤ c → |irtAux A r lam sel T d u c| ≤ D := by
  intro d
  induction d with
  | zero =>
    intro u
    refine ⟨max ((∑ j, lam j) * tau T u) 0 * ∑ j, r j + 0, fun c hc => ?_⟩
    have hb : 0 ≤ (fun l => c l / tau T u) := fun l =>
      div_nonneg (hc l) (irt_rd_tau_nonneg T hT u)
    obtain ⟨⟨_, hx0, hx1⟩, _⟩ := hsel _ hb
    rw [irtAux]
    exact irt_rd_window_abs A r lam hlam hr _ _
      (fun j => (irt_rd_plain_mem lam _ hlam hx0 hx1 j).1)
      (fun j => (irt_rd_plain_mem lam _ hlam hx0 hx1 j).2) c hc _ 0 (fun c' _ => by simp)
  | succ d ih =>
    intro u
    obtain ⟨D, hD⟩ := ih (u + 1)
    refine ⟨max ((∑ j, lam j) * (tau T u - tau T (u + 1))) 0 * ∑ j, r j + D, fun c hc => ?_⟩
    have hb : 0 ≤ (fun l => c l / tau T u) := fun l =>
      div_nonneg (hc l) (irt_rd_tau_nonneg T hT u)
    obtain ⟨⟨_, hx0, hx1⟩, _⟩ := hsel _ hb
    rw [irtAux]
    exact irt_rd_window_abs A r lam hlam hr _ _
      (fun j => (irt_rd_thr_mem lam _ _ hlam hx0 hx1 j).1)
      (fun j => (irt_rd_thr_mem lam _ _ hlam hx0 hx1 j).2) c hc _ D hD

/-! ### The re-solving schedule -/

lemma irt_rd_tau_zero (T : ℝ) : tau T 0 = T := by simp [tau]

lemma irt_rd_tau_tau_zero (T : ℝ) (u : ℕ) : tau (tau T u) 0 = tau T u := irt_rd_tau_zero _

lemma irt_rd_tau_tau_one (T : ℝ) (hT : 1 ≤ T) (u : ℕ) : tau (tau T u) 1 = tau T (u + 1) := by
  unfold tau
  rw [← Real.rpow_mul (by linarith), pow_one, pow_succ]

lemma irt_rd_one_le_tau (T : ℝ) (hT : 1 ≤ T) (u : ℕ) : 1 ≤ tau T u :=
  Real.one_le_rpow hT (by positivity)

lemma irt_rd_tau_pow (T : ℝ) (hT : 1 ≤ T) (u : ℕ) (a : ℝ) :
    tau T u ^ a = T ^ ((5 / 6 : ℝ) ^ u * a) := by
  unfold tau
  rw [← Real.rpow_mul (by linarith)]

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), IsDLPSelector A r lam sel →
      ∀ T : ℝ, 1 ≤ T → ∀ C : Fin m → ℝ, 0 ≤ C → ∀ K' : ℕ,
        hindsightValue A r lam T C - irtValue A r lam sel K' T C ≤
          M * (∑ u ∈ Finset.range K',
              T ^ ((5 / 6 : ℝ) ^ u) * Real.exp (-κ * T ^ ((5 / 6 : ℝ) ^ u / 6))) +
            M * T ^ ((5 / 6 : ℝ) ^ K' / 2) := by
  obtain ⟨κ, hκ, M₁, hM₁⟩ := prop1_one_resolve A r lam hlam hr hA
  obtain ⟨M₂, hM₂⟩ := spa_dlp_gap_sqrt A r lam hlam hr hA
  refine ⟨κ, hκ, max (max M₁ M₂) 0, fun sel hsel T hT C hC K' => ?_⟩
  set M := max (max M₁ M₂) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : M₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  set E : ℕ → ℝ := fun v => T ^ ((5 / 6 : ℝ) ^ v) * Real.exp (-κ * T ^ ((5 / 6 : ℝ) ^ v / 6))
    with hE
  have hE0 : ∀ v, 0 ≤ E v := fun v =>
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le
  -- the main induction over the number of remaining re-solves
  have key : ∀ d u : ℕ, ∀ c : Fin m → ℝ, 0 ≤ c →
      hindsightValue A r lam (tau T u) c - irtAux A r lam sel T d u c ≤
        M * (∑ v ∈ Finset.Ico u (u + d), E v) + M * T ^ ((5 / 6 : ℝ) ^ (u + d) / 2) := by
    intro d
    induction d with
    | zero =>
      intro u c hc
      have hτ1 := irt_rd_one_le_tau T hT u
      have hτ0 : 0 < tau T u := by linarith
      have h1 := hindsight_le_dlp A r lam hlam hr hA (tau T u) hτ0 c hc
      have h2 := hM₂ sel hsel (tau T u) hτ0 c hc
      have e : irtValue A r lam sel 0 (tau T u) c = irtAux A r lam sel T 0 u c := by
        simp only [irtValue, irtAux, irt_rd_tau_tau_zero]
      rw [e] at h2
      have hs : Real.sqrt (tau T u) = T ^ ((5 / 6 : ℝ) ^ (u + 0) / 2) := by
        rw [Real.sqrt_eq_rpow, irt_rd_tau_pow T hT u, add_zero]; ring_nf
      rw [hs] at h2
      have hX : 0 ≤ T ^ ((5 / 6 : ℝ) ^ (u + 0) / 2) := Real.rpow_nonneg (by linarith) _
      simp only [add_zero, Finset.Ico_self, Finset.sum_empty, mul_zero, zero_add] at hX h2 ⊢
      have : M₂ * T ^ ((5 / 6 : ℝ) ^ u / 2) ≤ M * T ^ ((5 / 6 : ℝ) ^ u / 2) :=
        mul_le_mul_of_nonneg_right hM2 hX
      linarith
    | succ d ih =>
      intro u c hc
      have hτ1 := irt_rd_one_le_tau T hT u
      have hτ0 : 0 < tau T u := by linarith
      have hb : 0 ≤ (fun l => c l / tau T u) := fun l => div_nonneg (hc l) hτ0.le
      obtain ⟨⟨_, hx0, hx1⟩, _⟩ := hsel _ hb
      -- Proposition 1, part 1, on the remaining horizon `τ_u`
      have hP1 := (hM₁ sel hsel (tau T u) hτ1 c hc).1
      have e1 : hoValue A r lam sel 1 (tau T u) c =
          windowValue A r lam (tau T u - tau T (u + 1))
            (thresholdProbs lam (tau T u) (sel fun l => c l / tau T u)) c
            (hindsightValue A r lam (tau T (u + 1))) := by
        simp only [hoValue, hoAux, irt_rd_tau_tau_zero, irt_rd_tau_tau_one T hT, zero_add]
      rw [e1] at hP1
      have e2 : tau T u ^ (1 / 6 : ℝ) = T ^ ((5 / 6 : ℝ) ^ u / 6) := by
        rw [irt_rd_tau_pow T hT u]; ring_nf
      rw [e2] at hP1
      have hP1' : hindsightValue A r lam (tau T u) c -
          windowValue A r lam (tau T u - tau T (u + 1))
            (thresholdProbs lam (tau T u) (sel fun l => c l / tau T u)) c
            (hindsightValue A r lam (tau T (u + 1))) ≤ M * E u := by
        refine le_trans hP1 ?_
        have : M₁ * tau T u * Real.exp (-κ * T ^ ((5 / 6 : ℝ) ^ u / 6)) = M₁ * E u := by
          simp only [hE, tau]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hM1 (hE0 u)
      -- the induction hypothesis, propagated through the window
      obtain ⟨D₂, hD₂⟩ := irt_rd_irt_abs A r lam hlam hr sel hsel T hT d (u + 1)
      have hτ1' := irt_rd_one_le_tau T hT (u + 1)
      set B := M * (∑ v ∈ Finset.Ico (u + 1) (u + 1 + d), E v) +
        M * T ^ ((5 / 6 : ℝ) ^ (u + 1 + d) / 2) with hBdef
      have hB0 : 0 ≤ B := by
        have : 0 ≤ ∑ v ∈ Finset.Ico (u + 1) (u + 1 + d), E v := sum_nonneg fun v _ => hE0 v
        have : 0 ≤ T ^ ((5 / 6 : ℝ) ^ (u + 1 + d) / 2) := Real.rpow_nonneg (by linarith) _
        positivity
      have hW := irt_rd_window_diff A r lam hlam hr (tau T u - tau T (u + 1))
        (thresholdProbs lam (tau T u) (sel fun l => c l / tau T u))
        (fun j => (irt_rd_thr_mem lam _ _ hlam hx0 hx1 j).1)
        (fun j => (irt_rd_thr_mem lam _ _ hlam hx0 hx1 j).2) c hc
        (hindsightValue A r lam (tau T (u + 1))) (irtAux A r lam sel T d (u + 1))
        _ D₂ B (irt_rd_ho_abs A r lam hlam hr hA _ (by linarith)) hD₂ hB0
        (fun c' hc' => ih (u + 1) c' hc')
      have e3 : irtAux A r lam sel T (d + 1) u c =
          windowValue A r lam (tau T u - tau T (u + 1))
            (thresholdProbs lam (tau T u) (sel fun l => c l / tau T u)) c
            (irtAux A r lam sel T d (u + 1)) := by
        rw [irtAux]
      rw [e3]
      have e4 : ∑ v ∈ Finset.Ico u (u + (d + 1)), E v =
          E u + ∑ v ∈ Finset.Ico (u + 1) (u + 1 + d), E v := by
        rw [show u + (d + 1) = u + 1 + d by ring]
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      rw [e4, show u + (d + 1) = u + 1 + d by ring]
      linarith
  have h := key K' 0 C hC
  rw [irt_rd_tau_zero, zero_add, ← Finset.range_eq_Ico] at h
  exact h
