-- Prove2me | solution 1 for ResolvingNRM.IRT.spa_dlp_gap_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:20:03.927482+00:00
-- url     : https://prove2.me/submissions/10eba598-b103-4a4b-a31a-13b21c14de1b

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix ResolvingNRM.IRT Finset

/-! ### Poisson moments -/

lemma irt_sp_exp_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (x : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h

lemma irt_sp_pmf_hasSum0 (μ : ℝ) (hμ : 0 ≤ μ) : HasSum (fun N : ℕ => poissonPMF μ N) 1 := by
  have h := (irt_sp_exp_hasSum μ).mul_left (Real.exp (-μ))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  have e : (fun N : ℕ => poissonPMF μ N) =
      fun N : ℕ => Real.exp (-μ) * (μ ^ N / (N.factorial : ℝ)) := by
    funext N
    unfold poissonPMF
    rw [max_eq_left hμ]
    ring
  rw [e]; exact h

lemma irt_sp_pmf_hasSum1 (μ : ℝ) (hμ : 0 ≤ μ) :
    HasSum (fun N : ℕ => poissonPMF μ N * (N : ℝ)) μ := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  have h := (irt_sp_pmf_hasSum0 μ hμ).mul_left μ
  rw [mul_one] at h
  have e : (fun N : ℕ => poissonPMF μ (N + 1) * ((N + 1 : ℕ) : ℝ)) =
      fun N : ℕ => μ * poissonPMF μ N := by
    funext N
    unfold poissonPMF
    rw [max_eq_left hμ, Nat.factorial_succ]
    push_cast
    have : (N.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [e]; exact h

lemma irt_sp_pmf_hasSum2 (μ : ℝ) (hμ : 0 ≤ μ) :
    HasSum (fun N : ℕ => poissonPMF μ N * ((N : ℝ) * ((N : ℝ) - 1))) (μ ^ 2) := by
  rw [← hasSum_nat_add_iff' 2]
  simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one, zero_mul,
    mul_zero, sub_self, zero_add, add_zero, sub_zero]
  have h := (irt_sp_pmf_hasSum0 μ hμ).mul_left (μ ^ 2)
  rw [mul_one] at h
  have e : (fun N : ℕ => poissonPMF μ (N + 2) * (((N + 2 : ℕ) : ℝ) * (((N + 2 : ℕ) : ℝ) - 1))) =
      fun N : ℕ => μ ^ 2 * poissonPMF μ N := by
    funext N
    unfold poissonPMF
    rw [max_eq_left hμ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have : (N.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [e]; exact h

/-! ### Product-form sums over classes and coins -/

lemma irt_sp_prod_sum {n N : ℕ} (u : Fin N → Fin n → Bool → ℝ) :
    ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, ∏ i, u i (cls i) (coin i) =
      ∏ i, ∑ j, ∑ b, u i j b := by
  have h1 : ∀ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, ∏ i, u i (cls i) (coin i) =
      ∏ i, ∑ b, u i (cls i) b := fun cls =>
    (Fintype.prod_sum (fun i (b : Bool) => u i (cls i) b)).symm
  rw [Fintype.sum_congr _ _ h1]
  exact (Fintype.prod_sum (fun i (j : Fin n) => ∑ b, u i j b)).symm

/-- The per-arrival weight. -/
noncomputable def irtSpOmega {n : ℕ} (lam p : Fin n → ℝ) (j : Fin n) (b : Bool) : ℝ :=
  (lam j / ∑ j', lam j') * (if b = true then p j else 1 - p j)

lemma irt_sp_omega_sum {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (hn : 0 < n) :
    ∑ j, ∑ b, irtSpOmega lam p j b = 1 := by
  have hΛ : 0 < ∑ j, lam j := by
    have : lam ⟨0, hn⟩ ≤ ∑ j, lam j :=
      single_le_sum (f := lam) (fun j _ => (hlam j).le) (mem_univ _)
    linarith [hlam ⟨0, hn⟩]
  unfold irtSpOmega
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  have : ∀ j, (lam j / ∑ j', lam j') * p j + (lam j / ∑ j', lam j') * (1 - p j) =
      lam j / ∑ j', lam j' := fun j => by ring
  simp_rw [this]
  rw [← sum_div, div_self hΛ.ne']

/-- Expectation over the classes and coins of `N` arrivals. -/
noncomputable def irtSpEx {n : ℕ} (lam p : Fin n → ℝ) (N : ℕ)
    (F : (Fin N → Fin n) → (Fin N → Bool) → ℝ) : ℝ :=
  ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
    (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
      F cls coin

lemma irt_sp_ex_add {n : ℕ} (lam p : Fin n → ℝ) (N : ℕ) (F G : (Fin N → Fin n) → (Fin N → Bool) → ℝ) :
    irtSpEx lam p N (fun a b => F a b + G a b) = irtSpEx lam p N F + irtSpEx lam p N G := by
  unfold irtSpEx
  rw [← sum_add_distrib]
  congr 1; ext cls
  rw [← sum_add_distrib]
  congr 1; ext coin
  ring

lemma irt_sp_ex_sub {n : ℕ} (lam p : Fin n → ℝ) (N : ℕ) (F G : (Fin N → Fin n) → (Fin N → Bool) → ℝ) :
    irtSpEx lam p N (fun a b => F a b - G a b) = irtSpEx lam p N F - irtSpEx lam p N G := by
  unfold irtSpEx
  rw [← sum_sub_distrib]
  congr 1; ext cls
  rw [← sum_sub_distrib]
  congr 1; ext coin
  ring

lemma irt_sp_ex_smul {n : ℕ} (lam p : Fin n → ℝ) (N : ℕ) (c : ℝ)
    (F : (Fin N → Fin n) → (Fin N → Bool) → ℝ) :
    irtSpEx lam p N (fun a b => c * F a b) = c * irtSpEx lam p N F := by
  unfold irtSpEx
  rw [mul_sum]
  congr 1; ext cls
  rw [mul_sum]
  congr 1; ext coin
  ring

lemma irt_sp_ex_finsum {n : ℕ} (lam p : Fin n → ℝ) (N : ℕ) {ι : Type*} (s : Finset ι)
    (F : ι → (Fin N → Fin n) → (Fin N → Bool) → ℝ) :
    irtSpEx lam p N (fun a b => ∑ l ∈ s, F l a b) = ∑ l ∈ s, irtSpEx lam p N (F l) := by
  unfold irtSpEx
  simp_rw [mul_sum]
  calc _ = ∑ cls : Fin N → Fin n, ∑ l ∈ s, ∑ coin : Fin N → Bool,
        (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
          F l cls coin := sum_congr rfl (fun cls _ => sum_comm)
    _ = _ := sum_comm

lemma irt_sp_ex_mono {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (N : ℕ)
    (F G : (Fin N → Fin n) → (Fin N → Bool) → ℝ) (h : ∀ a b, F a b ≤ G a b) :
    irtSpEx lam p N F ≤ irtSpEx lam p N G := by
  unfold irtSpEx
  apply sum_le_sum; intro cls _
  apply sum_le_sum; intro coin _
  apply mul_le_mul_of_nonneg_left (h cls coin)
  apply prod_nonneg
  intro i _
  have hΛ : 0 ≤ ∑ j, lam j := sum_nonneg fun j _ => (hlam j).le
  have h1 : 0 ≤ lam (cls i) / ∑ j, lam j := div_nonneg (hlam _).le hΛ
  have h2 : 0 ≤ (if coin i then p (cls i) else 1 - p (cls i)) := by
    split_ifs
    · exact hp0 _
    · linarith [hp1 (cls i)]
  exact mul_nonneg h1 h2

lemma irt_sp_ex_const {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (hn : 0 < n)
    (N : ℕ) (c : ℝ) : irtSpEx lam p N (fun _ _ => c) = c := by
  unfold irtSpEx
  simp_rw [← sum_mul]
  have := irt_sp_prod_sum (fun (_ : Fin N) j b => irtSpOmega lam p j b)
  unfold irtSpOmega at this
  rw [this]
  have h := irt_sp_omega_sum lam p hlam hn
  unfold irtSpOmega at h
  rw [h]
  simp

lemma irt_sp_ex_one_point {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (hn : 0 < n)
    (N : ℕ) (i0 : Fin N) (f : Fin n → Bool → ℝ) :
    irtSpEx lam p N (fun cls coin => f (cls i0) (coin i0)) =
      ∑ j, ∑ b, irtSpOmega lam p j b * f j b := by
  unfold irtSpEx
  have e : ∀ (cls : Fin N → Fin n) (coin : Fin N → Bool),
      (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
        f (cls i0) (coin i0) =
      ∏ i, (irtSpOmega lam p (cls i) (coin i) *
        (if i = i0 then f (cls i) (coin i) else 1)) := by
    intro cls coin
    conv_rhs => rw [prod_mul_distrib, prod_ite_eq' univ i0 (fun i => f (cls i) (coin i))]
    simp [irtSpOmega]
  simp_rw [e]
  rw [irt_sp_prod_sum (fun i j b => irtSpOmega lam p j b * (if i = i0 then f j b else 1))]
  have e2 : ∀ i, ∑ j, ∑ b, irtSpOmega lam p j b * (if i = i0 then f j b else 1) =
      if i = i0 then ∑ j, ∑ b, irtSpOmega lam p j b * f j b else 1 := by
    intro i
    split_ifs
    · rfl
    · simp only [mul_one]; exact irt_sp_omega_sum lam p hlam hn
  simp_rw [e2]
  rw [prod_ite_eq' univ i0 (fun _ => ∑ j, ∑ b, irtSpOmega lam p j b * f j b)]
  simp

lemma irt_sp_ex_two_point {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (hn : 0 < n)
    (N : ℕ) (i0 i1 : Fin N) (h01 : i0 ≠ i1) (f g : Fin n → Bool → ℝ) :
    irtSpEx lam p N (fun cls coin => f (cls i0) (coin i0) * g (cls i1) (coin i1)) =
      (∑ j, ∑ b, irtSpOmega lam p j b * f j b) * (∑ j, ∑ b, irtSpOmega lam p j b * g j b) := by
  unfold irtSpEx
  have e : ∀ (cls : Fin N → Fin n) (coin : Fin N → Bool),
      (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
        (f (cls i0) (coin i0) * g (cls i1) (coin i1)) =
      ∏ i, (irtSpOmega lam p (cls i) (coin i) *
        ((if i = i0 then f (cls i) (coin i) else 1) * (if i = i1 then g (cls i) (coin i) else 1))) := by
    intro cls coin
    conv_rhs => rw [prod_mul_distrib, prod_mul_distrib,
      prod_ite_eq' univ i0 (fun i => f (cls i) (coin i)),
      prod_ite_eq' univ i1 (fun i => g (cls i) (coin i))]
    simp [irtSpOmega]
  simp_rw [e]
  rw [irt_sp_prod_sum (fun i j b => irtSpOmega lam p j b *
    ((if i = i0 then f j b else 1) * (if i = i1 then g j b else 1)))]
  have e2 : ∀ i, ∑ j, ∑ b, irtSpOmega lam p j b *
      ((if i = i0 then f j b else 1) * (if i = i1 then g j b else 1)) =
      (if i = i0 then ∑ j, ∑ b, irtSpOmega lam p j b * f j b else 1) *
        (if i = i1 then ∑ j, ∑ b, irtSpOmega lam p j b * g j b else 1) := by
    intro i
    by_cases h0 : i = i0
    · simp only [h0, if_true, h01, if_false, mul_one]
    · by_cases h1 : i = i1
      · simp only [h1, if_true, h01.symm, if_false, one_mul]
      · simp only [h0, h1, if_false, mul_one]
        exact irt_sp_omega_sum lam p hlam hn
  simp_rw [e2]
  rw [prod_mul_distrib, prod_ite_eq' univ i0 (fun _ => ∑ j, ∑ b, irtSpOmega lam p j b * f j b),
    prod_ite_eq' univ i1 (fun _ => ∑ j, ∑ b, irtSpOmega lam p j b * g j b)]
  simp

/-- `∑_i φ(class_i, coin_i)`. -/
def irtSpLin {n N : ℕ} (φ : Fin n → Bool → ℝ) (cls : Fin N → Fin n) (coin : Fin N → Bool) : ℝ :=
  ∑ i, φ (cls i) (coin i)

lemma irt_sp_ex_lin {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (hn : 0 < n)
    (N : ℕ) (φ : Fin n → Bool → ℝ) :
    irtSpEx lam p N (fun cls coin => irtSpLin φ cls coin) =
      (N : ℝ) * ∑ j, ∑ b, irtSpOmega lam p j b * φ j b := by
  unfold irtSpLin
  rw [irt_sp_ex_finsum lam p N univ (fun i cls coin => φ (cls i) (coin i))]
  simp_rw [irt_sp_ex_one_point lam p hlam hn N _ φ]
  simp

lemma irt_sp_ex_lin_sq {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (hn : 0 < n)
    (N : ℕ) (φ : Fin n → Bool → ℝ) :
    irtSpEx lam p N (fun cls coin => irtSpLin φ cls coin ^ 2) =
      (N : ℝ) * ∑ j, ∑ b, irtSpOmega lam p j b * (φ j b * φ j b) +
        (N : ℝ) * ((N : ℝ) - 1) * (∑ j, ∑ b, irtSpOmega lam p j b * φ j b) ^ 2 := by
  unfold irtSpLin
  have e : ∀ (cls : Fin N → Fin n) (coin : Fin N → Bool),
      (∑ i, φ (cls i) (coin i)) ^ 2 = ∑ i, ∑ i', φ (cls i) (coin i) * φ (cls i') (coin i') := by
    intro cls coin
    rw [sq, sum_mul_sum]
  simp_rw [e]
  rw [irt_sp_ex_finsum lam p N univ (fun i cls coin => ∑ i', φ (cls i) (coin i) * φ (cls i') (coin i'))]
  simp_rw [irt_sp_ex_finsum lam p N univ (fun i' cls coin => φ (cls _) (coin _) * φ (cls i') (coin i'))]
  set a := ∑ j, ∑ b, irtSpOmega lam p j b * (φ j b * φ j b)
  set c := ∑ j, ∑ b, irtSpOmega lam p j b * φ j b
  have e2 : ∀ i i' : Fin N, irtSpEx lam p N (fun cls coin => φ (cls i) (coin i) * φ (cls i') (coin i')) =
      if i = i' then a else c ^ 2 := by
    intro i i'
    split_ifs with h
    · subst h
      exact irt_sp_ex_one_point lam p hlam hn N i (fun j b => φ j b * φ j b)
    · rw [irt_sp_ex_two_point lam p hlam hn N i i' h φ φ, sq]
  simp_rw [e2]
  have e3 : ∀ i : Fin N, ∑ i' : Fin N, (if i = i' then a else c ^ 2) = a + ((N : ℝ) - 1) * c ^ 2 := by
    intro i
    have : ∑ i' : Fin N, (if i = i' then a else c ^ 2) =
        ∑ i' : Fin N, ((if i = i' then (a - c ^ 2) else 0) + c ^ 2) := by
      congr 1; ext i'; split_ifs <;> ring
    rw [this, sum_add_distrib, sum_ite_eq]
    simp
    ring
  simp_rw [e3]
  simp
  ring
lemma irt_sq_pmf_nonneg (μ : ℝ) (k : ℕ) : 0 ≤ poissonPMF μ k := by
  unfold poissonPMF
  have : 0 ≤ max μ 0 := le_max_right _ _
  positivity

lemma irt_sq_pmf_sum_le (μ : ℝ) (N : ℕ) : ∑ i ∈ range N, poissonPMF μ i ≤ 1 := by
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

lemma irt_sq_pmf_mean_le (μ : ℝ) (N : ℕ) :
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
        mul_le_mul_of_nonneg_left (irt_sq_pmf_sum_le μ N) hμ
    _ = max μ 0 := mul_one _

lemma irt_sq_pmf_summable (μ : ℝ) : Summable (fun N => poissonPMF μ N) :=
  summable_of_sum_range_le (fun N => irt_sq_pmf_nonneg μ N) (irt_sq_pmf_sum_le μ)

lemma irt_sq_pmf_tsum_le (μ : ℝ) : ∑' N, poissonPMF μ N ≤ 1 :=
  Real.tsum_le_of_sum_range_le (fun N => irt_sq_pmf_nonneg μ N) (irt_sq_pmf_sum_le μ)

lemma irt_sq_pmf_lin_summable (μ R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    Summable (fun N : ℕ => poissonPMF μ N * ((N : ℝ) * R + D)) := by
  refine summable_of_sum_range_le (c := max μ 0 * R + D)
    (fun N => mul_nonneg (irt_sq_pmf_nonneg μ N) (by positivity)) (fun N => ?_)
  have e : ∑ i ∈ range N, poissonPMF μ i * ((i : ℝ) * R + D) =
      R * ∑ i ∈ range N, poissonPMF μ i * (i : ℝ) + D * ∑ i ∈ range N, poissonPMF μ i := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; congr 1; ext i; ring
  rw [e]
  have h1 := irt_sq_pmf_mean_le μ N
  have h2 := irt_sq_pmf_sum_le μ N
  nlinarith

/-! ### One run of a probabilistic allocation -/

lemma irt_sq_runWindow_bounds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
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

lemma irt_sq_wt_nonneg {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
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

lemma irt_sq_wt_sum_le {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (N : ℕ) :
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

lemma irt_sq_inner_abs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
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
    have hw := irt_sq_wt_nonneg lam p hlam hp0 hp1 N cls coin
    obtain ⟨h1, h2, h3⟩ := irt_sq_runWindow_bounds A r hr
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
  have := irt_sq_wt_sum_le lam p hlam N
  have h0 : 0 ≤ (N : ℝ) * ∑ j, r j + D := by positivity
  nlinarith

lemma irt_sq_window_summable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
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
  refine Summable.of_norm_bounded (irt_sq_pmf_lin_summable ((∑ j, lam j) * ℓ) _ D hR hD) ?_
  intro N
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (irt_sq_pmf_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left
    (irt_sq_inner_abs A r lam hlam hr p hp0 hp1 c hc W D hW N) (irt_sq_pmf_nonneg _ _)


/-! ### Sample-path bound for one run -/

/-- `∑` over the accepted-coin arrivals of a list of `φ(class)`. -/
noncomputable def irtSpLinL {n : ℕ} (φ : Fin n → ℝ) (L : List (Fin n × Bool)) : ℝ :=
  (L.map fun q => if q.2 = true then φ q.1 else 0).sum

lemma irt_sp_linL_cons {n : ℕ} (φ : Fin n → ℝ) (j : Fin n) (b : Bool) (L : List (Fin n × Bool)) :
    irtSpLinL φ ((j, b) :: L) = (if b = true then φ j else 0) + irtSpLinL φ L := by
  simp [irtSpLinL]

lemma irt_sp_linL_nonneg {n : ℕ} (φ : Fin n → ℝ) (hφ : ∀ j, 0 ≤ φ j) (L : List (Fin n × Bool)) :
    0 ≤ irtSpLinL φ L := by
  induction L with
  | nil => simp [irtSpLinL]
  | cons a rest ih =>
    obtain ⟨j, b⟩ := a
    rw [irt_sp_linL_cons]
    have : 0 ≤ (if b = true then φ j else 0) := by split_ifs <;> simp [hφ j]
    linarith

lemma irt_sp_linL_ofFn {n N : ℕ} (φ : Fin n → ℝ) (cls : Fin N → Fin n) (coin : Fin N → Bool) :
    irtSpLinL φ (List.ofFn fun i => (cls i, coin i)) =
      irtSpLin (fun j b => if b = true then φ j else 0) cls coin := by
  simp [irtSpLinL, irtSpLin, List.sum_ofFn]

lemma irt_sp_sample {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : ∀ l j, 0 ≤ A l j) (ρ Amax : ℝ) (hρ : 0 ≤ ρ)
    (hrA : ∀ l j, 0 < A l j → r j ≤ ρ * A l j) (hAmax : ∀ l j, A l j ≤ Amax)
    (L : List (Fin n × Bool)) :
    ∀ c : Fin m → ℝ, 0 ≤ c →
      irtSpLinL r L - ρ * ∑ l, max 0 (irtSpLinL (fun j => A l j) L - c l + Amax) ≤
        (runWindow A r L c).1 := by
  induction L with
  | nil =>
    intro c hc
    simp only [irtSpLinL, List.map_nil, List.sum_nil, runWindow]
    have : ∀ l, max 0 (0 - c l + Amax) ≥ 0 := fun l => le_max_left _ _
    have : 0 ≤ ∑ l, max 0 (0 - c l + Amax) := sum_nonneg fun l _ => le_max_left _ _
    nlinarith
  | cons a rest ih =>
    intro c hc
    obtain ⟨j, b⟩ := a
    simp only [irt_sp_linL_cons]
    by_cases h : b = true ∧ ∀ l, A l j ≤ c l
    · have hc' : 0 ≤ (fun l => c l - A l j) := fun l => by
        have := h.2 l; simp only [Pi.zero_apply]; linarith
      have ih' := ih _ hc'
      simp only [runWindow, if_pos h]
      rw [if_pos h.1]
      have e : ∀ l, (if b = true then A l j else 0) + irtSpLinL (fun j => A l j) rest - c l + Amax =
          irtSpLinL (fun j => A l j) rest - (c l - A l j) + Amax := by
        intro l; rw [if_pos h.1]; ring
      simp_rw [e]
      linarith
    · by_cases hb : b = true
      · -- rejected for lack of capacity
        have hex : ∃ l0, c l0 < A l0 j := by
          by_contra hne
          push_neg at hne
          exact h ⟨hb, hne⟩
        obtain ⟨l0, hl0⟩ := hex
        have ih' := ih c hc
        simp only [runWindow, if_neg h]
        simp only [hb, if_true]
        have hX : ∀ l, 0 ≤ irtSpLinL (fun j => A l j) rest := fun l =>
          irt_sp_linL_nonneg _ (fun j => hA l j) rest
        have hmono : ∀ l, max 0 (irtSpLinL (fun j => A l j) rest - c l + Amax) ≤
            max 0 (A l j + irtSpLinL (fun j => A l j) rest - c l + Amax) := by
          intro l
          apply max_le_max le_rfl
          linarith [hA l j]
        have hl0' : max 0 (irtSpLinL (fun j => A l0 j) rest - c l0 + Amax) + A l0 j ≤
            max 0 (A l0 j + irtSpLinL (fun j => A l0 j) rest - c l0 + Amax) := by
          have h1 : 0 ≤ irtSpLinL (fun j => A l0 j) rest - c l0 + Amax := by
            linarith [hX l0, hAmax l0 j]
          rw [max_eq_right h1, max_eq_right (by linarith [hA l0 j])]
          linarith
        have hsum : ∑ l, max 0 (irtSpLinL (fun j => A l j) rest - c l + Amax) + A l0 j ≤
            ∑ l, max 0 (A l j + irtSpLinL (fun j => A l j) rest - c l + Amax) := by
          rw [← add_sum_erase _ _ (mem_univ l0), ← add_sum_erase _ _ (mem_univ l0)]
          have := sum_le_sum (s := univ.erase l0) fun l _ => hmono l
          linarith
        have hpos : 0 < A l0 j := lt_of_le_of_lt (hc l0) hl0
        have hr := hrA l0 j hpos
        nlinarith
      · have ih' := ih c hc
        simp only [runWindow, if_neg h]
        simp only [hb, Bool.false_eq_true, if_false, zero_add]
        exact ih'

/-! ### The static probabilistic allocation -/

lemma irt_sp_abs_le (w s : ℝ) (hs : 0 < s) : |w| ≤ w ^ 2 / (2 * s) + s / 2 := by
  rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
  have h1 : |w| ^ 2 = w ^ 2 := sq_abs w
  nlinarith [sq_nonneg (|w| - s), abs_nonneg w]

lemma irt_sp_omega_lin {n : ℕ} (lam x : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (a : Fin n → ℝ)
    (T : ℝ) :
    (∑ j, lam j) * T * ∑ j, ∑ b, irtSpOmega lam (plainProbs lam x) j b *
      (if b = true then a j else 0) = T * ∑ j, a j * x j := by
  unfold irtSpOmega plainProbs
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, mul_zero, add_zero]
  rw [mul_sum, mul_sum]
  congr 1; ext j
  have := (hlam j).ne'
  rcases eq_or_lt_of_le (sum_nonneg fun j _ => (hlam j).le : (0:ℝ) ≤ ∑ j, lam j) with h | h
  · have : lam j ≤ ∑ j, lam j := single_le_sum (f := lam) (fun j _ => (hlam j).le) (mem_univ j)
    linarith [hlam j]
  · field_simp

lemma irt_sp_phi_sq {n : ℕ} (a : Fin n → ℝ) (j : Fin n) (b : Bool) :
    (if b = true then a j else 0) * (if b = true then a j else 0) =
      if b = true then a j * a j else 0 := by
  cases b <;> simp

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), IsDLPSelector A r lam sel →
      ∀ T : ℝ, 0 < T → ∀ C : Fin m → ℝ, 0 ≤ C →
        dlpValue A r lam T C - irtValue A r lam sel 0 T C ≤ M * Real.sqrt T := by
  -- constants
  set ρ : ℝ := ∑ l, ∑ j, (if 0 < A l j then r j / A l j else 0) with hρdef
  set Amax : ℝ := ∑ l, ∑ j, A l j with hAmaxdef
  have hρ0 : 0 ≤ ρ := sum_nonneg fun l _ => sum_nonneg fun j _ => by
    split_ifs with h
    · exact div_nonneg (hr j) h.le
    · exact le_rfl
  have hrA : ∀ l j, 0 < A l j → r j ≤ ρ * A l j := by
    intro l j h
    have h1 : r j / A l j ≤ ρ := by
      have e1 : r j / A l j = (if 0 < A l j then r j / A l j else 0) := by rw [if_pos h]
      rw [e1]
      refine le_trans ?_ (single_le_sum (f := fun l => ∑ j, (if 0 < A l j then r j / A l j else 0))
        (fun l _ => sum_nonneg fun j _ => by
          split_ifs with h
          · exact div_nonneg (hr j) h.le
          · exact le_rfl) (mem_univ l))
      exact single_le_sum (f := fun j => (if 0 < A l j then r j / A l j else 0))
        (fun j _ => by
          split_ifs with h
          · exact div_nonneg (hr j) h.le
          · exact le_rfl) (mem_univ j)
    rwa [div_le_iff₀ h] at h1
  have hAmax : ∀ l j, A l j ≤ Amax := by
    intro l j
    refine le_trans ?_ (single_le_sum (f := fun l => ∑ j, A l j)
      (fun l _ => sum_nonneg fun j _ => hA l j) (mem_univ l))
    exact single_le_sum (f := fun j => A l j) (fun j _ => hA l j) (mem_univ j)
  have hAmax0 : 0 ≤ Amax := sum_nonneg fun l _ => sum_nonneg fun j _ => hA l j
  set Wv : Fin m → ℝ := fun l => ∑ j, A l j * A l j * lam j with hWv
  have hWv0 : ∀ l, 0 ≤ Wv l := fun l => sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hA l j) (hA l j)) (hlam j).le
  have hrl0 : 0 ≤ r ⬝ᵥ lam := sum_nonneg fun j _ => mul_nonneg (hr j) (hlam j).le
  set K1 : ℝ := ∑ l, ρ * (Wv l / 2 + 1 / 2 + Amax) with hK1
  have hK10 : 0 ≤ K1 := sum_nonneg fun l _ => mul_nonneg hρ0 (by linarith [hWv0 l])
  refine ⟨K1 + r ⬝ᵥ lam, fun sel hsel T hT C hC => ?_⟩
  set s := Real.sqrt T with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hT
  have hss : s * s = T := Real.mul_self_sqrt hT.le
  -- the LP solution and the policy
  have hb : 0 ≤ (fun l => C l / T) := fun l => div_nonneg (hC l) hT.le
  obtain ⟨⟨hx1, hx0, hxl⟩, hxopt⟩ := hsel _ hb
  set x := sel fun l => C l / T with hxdef
  set p := plainProbs lam x with hpdef
  have hp0 : ∀ j, 0 ≤ p j := fun j => div_nonneg (hx0 j) (hlam j).le
  have hp1 : ∀ j, p j ≤ 1 := fun j => (div_le_one (hlam j)).mpr (hxl j)
  have hdlp : dlpValue A r lam T C = T * (r ⬝ᵥ x) := by
    unfold dlpValue piValue
    congr 1
    apply IsGreatest.csSup_eq
    refine ⟨⟨x, hx1, hx0, hxl, rfl⟩, ?_⟩
    rintro v ⟨y, h1, h2, h3, rfl⟩
    exact hxopt y h1 h2 h3
  have hrx : r ⬝ᵥ x ≤ r ⬝ᵥ lam := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hxl j) (hr j)
  have hspa : irtValue A r lam sel 0 T C =
      ∑' N : ℕ, poissonPMF ((∑ j, lam j) * T) N *
        irtSpEx lam p N (fun cls coin => (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).1) := by
    simp only [irtValue, irtAux, windowValue, irtSpEx, tau, pow_zero, Real.rpow_one, add_zero]
    rfl
  have hsumm := irt_sq_window_summable A r lam hlam hr T p hp0 hp1 C hC (fun _ => 0) 0
    (fun _ _ => by simp)
  have hsumm' : Summable (fun N : ℕ => poissonPMF ((∑ j, lam j) * T) N *
      irtSpEx lam p N (fun cls coin => (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).1)) := by
    simpa [irtSpEx] using hsumm
  have hspa0 : 0 ≤ irtValue A r lam sel 0 T C := by
    rw [hspa]
    refine tsum_nonneg fun N => mul_nonneg (irt_sq_pmf_nonneg _ _) ?_
    unfold irtSpEx
    exact sum_nonneg fun cls _ => sum_nonneg fun coin _ =>
      mul_nonneg (irt_sq_wt_nonneg lam p hlam hp0 hp1 N cls coin)
        (irt_sq_runWindow_bounds A r hr _ C hC).1
  -- trivial regime: `T ≤ 1` or no classes
  by_cases htriv : T ≤ 1 ∨ n = 0
  · have hT1 : T * (r ⬝ᵥ lam) ≤ s * (r ⬝ᵥ lam) := by
      rcases htriv with h | h
      · have : T ≤ s := by
          rw [hs]
          have := Real.sqrt_le_sqrt h
          rw [Real.sqrt_one] at this
          nlinarith [Real.sq_sqrt hT.le]
        exact mul_le_mul_of_nonneg_right this hrl0
      · subst h; simp [dotProduct]
    rw [hdlp]
    have : T * (r ⬝ᵥ x) ≤ T * (r ⬝ᵥ lam) := mul_le_mul_of_nonneg_left hrx hT.le
    nlinarith
  push_neg at htriv
  obtain ⟨hT1, hn0⟩ := htriv
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hs1 : 1 ≤ s := by
    rw [hs, show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hT1.le
  -- the lower integrand
  set e : Fin m → ℝ := fun l => T * (A *ᵥ x) l with hedef
  have he : ∀ l, e l ≤ C l := by
    intro l
    have := hx1 l
    simp only at this
    rw [hedef]; dsimp only
    rw [le_div_iff₀ hT] at this
    linarith
  set φr : Fin n → Bool → ℝ := fun j b => if b = true then r j else 0 with hφr
  set φ : Fin m → Fin n → Bool → ℝ := fun l j b => if b = true then A l j else 0 with hφ
  set G : (N : ℕ) → (Fin N → Fin n) → (Fin N → Bool) → ℝ := fun N cls coin =>
    irtSpLin φr cls coin - ∑ l, ((ρ / (2 * s)) * irtSpLin (φ l) cls coin ^ 2 +
      (-(ρ / (2 * s)) * (2 * e l)) * irtSpLin (φ l) cls coin +
        ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax)) with hG
  have hGle : ∀ N (cls : Fin N → Fin n) (coin : Fin N → Bool),
      G N cls coin ≤ (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).1 := by
    intro N cls coin
    have hsp := irt_sp_sample A r hA ρ Amax hρ0 hrA hAmax (List.ofFn fun i => (cls i, coin i)) C hC
    simp only [irt_sp_linL_ofFn] at hsp
    refine le_trans ?_ hsp
    simp only [hG]
    have : ∀ l, max 0 (irtSpLin (fun j b => if b = true then A l j else 0) cls coin - C l + Amax) ≤
        (1 / (2 * s)) * irtSpLin (φ l) cls coin ^ 2 + (-(1 / (2 * s)) * (2 * e l)) *
          irtSpLin (φ l) cls coin + (e l ^ 2 / (2 * s) + s / 2 + Amax) := by
      intro l
      have h1 := irt_sp_abs_le (irtSpLin (φ l) cls coin - e l) s hs0
      have h2 : irtSpLin (φ l) cls coin - e l ≤ |irtSpLin (φ l) cls coin - e l| := le_abs_self _
      have hle := he l
      apply max_le
      · have : 0 ≤ (irtSpLin (φ l) cls coin - e l) ^ 2 / (2 * s) := by positivity
        have : (1 / (2 * s)) * irtSpLin (φ l) cls coin ^ 2 + (-(1 / (2 * s)) * (2 * e l)) *
          irtSpLin (φ l) cls coin + (e l ^ 2 / (2 * s) + s / 2 + Amax) =
            (irtSpLin (φ l) cls coin - e l) ^ 2 / (2 * s) + s / 2 + Amax := by
          field_simp; ring
        rw [this]; linarith
      · have : (1 / (2 * s)) * irtSpLin (φ l) cls coin ^ 2 + (-(1 / (2 * s)) * (2 * e l)) *
          irtSpLin (φ l) cls coin + (e l ^ 2 / (2 * s) + s / 2 + Amax) =
            (irtSpLin (φ l) cls coin - e l) ^ 2 / (2 * s) + s / 2 + Amax := by
          field_simp; ring
        rw [this, hφ]; dsimp only; linarith
    have hsum := sum_le_sum fun l (_ : l ∈ univ) => this l
    have : ρ * ∑ l, max 0 (irtSpLin (fun j b => if b = true then A l j else 0) cls coin - C l + Amax)
        ≤ ∑ l, (ρ / (2 * s) * irtSpLin (φ l) cls coin ^ 2 + -(ρ / (2 * s)) * (2 * e l) *
          irtSpLin (φ l) cls coin + ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax)) := by
      rw [mul_sum]
      refine sum_le_sum fun l _ => ?_
      have := mul_le_mul_of_nonneg_left (this l) hρ0
      have e' : ρ * ((1 / (2 * s)) * irtSpLin (φ l) cls coin ^ 2 + (-(1 / (2 * s)) * (2 * e l)) *
          irtSpLin (φ l) cls coin + (e l ^ 2 / (2 * s) + s / 2 + Amax)) =
          ρ / (2 * s) * irtSpLin (φ l) cls coin ^ 2 + -(ρ / (2 * s)) * (2 * e l) *
            irtSpLin (φ l) cls coin + ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax) := by ring
      linarith
    linarith
  -- its expectation for `N` arrivals
  set α : ℝ := ∑ j, ∑ b, irtSpOmega lam p j b * φr j b
  set P : Fin m → ℝ := fun l => ∑ j, ∑ b, irtSpOmega lam p j b * φ l j b
  set Q : Fin m → ℝ := fun l => ∑ j, ∑ b, irtSpOmega lam p j b * (φ l j b * φ l j b)
  have hEG : ∀ N, irtSpEx lam p N (G N) = (N : ℝ) * α - ∑ l, ((ρ / (2 * s)) *
      ((N : ℝ) * Q l + (N : ℝ) * ((N : ℝ) - 1) * P l ^ 2) +
      (-(ρ / (2 * s)) * (2 * e l)) * ((N : ℝ) * P l) + ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax)) := by
    intro N
    simp only [hG]
    rw [irt_sp_ex_sub, irt_sp_ex_lin lam p hlam hn, irt_sp_ex_finsum]
    congr 1
    refine sum_congr rfl fun l _ => ?_
    rw [irt_sp_ex_add, irt_sp_ex_add, irt_sp_ex_smul, irt_sp_ex_smul, irt_sp_ex_const lam p hlam hn,
      irt_sp_ex_lin_sq lam p hlam hn, irt_sp_ex_lin lam p hlam hn]
  -- summing over `N`
  set μ : ℝ := (∑ j, lam j) * T with hμ
  have hμ0 : 0 ≤ μ := mul_nonneg (sum_nonneg fun j _ => (hlam j).le) hT.le
  have H0 := irt_sp_pmf_hasSum0 μ hμ0
  have H1 := irt_sp_pmf_hasSum1 μ hμ0
  have H2 := irt_sp_pmf_hasSum2 μ hμ0
  have hHS : HasSum (fun N : ℕ => poissonPMF μ N * irtSpEx lam p N (G N))
      (μ * α - ∑ l, ((ρ / (2 * s)) * (μ * Q l + μ ^ 2 * P l ^ 2) +
        (-(ρ / (2 * s)) * (2 * e l)) * (μ * P l) + ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax))) := by
    have hl : ∀ l ∈ (univ : Finset (Fin m)), HasSum (fun N : ℕ => poissonPMF μ N *
        ((ρ / (2 * s)) * ((N : ℝ) * Q l + (N : ℝ) * ((N : ℝ) - 1) * P l ^ 2) +
          (-(ρ / (2 * s)) * (2 * e l)) * ((N : ℝ) * P l) + ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax)))
        ((ρ / (2 * s)) * (μ * Q l + μ ^ 2 * P l ^ 2) +
          (-(ρ / (2 * s)) * (2 * e l)) * (μ * P l) + ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax)) := by
      intro l _
      have := (((H1.mul_left ((ρ / (2 * s)) * Q l)).add (H2.mul_left ((ρ / (2 * s)) * P l ^ 2))).add
        (H1.mul_left ((-(ρ / (2 * s)) * (2 * e l)) * P l))).add
        (H0.mul_left (ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax)))
      rw [show (ρ / (2 * s)) * (μ * Q l + μ ^ 2 * P l ^ 2) +
          (-(ρ / (2 * s)) * (2 * e l)) * (μ * P l) + ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax) =
          (ρ / (2 * s)) * Q l * μ + (ρ / (2 * s)) * P l ^ 2 * μ ^ 2 +
            (-(ρ / (2 * s)) * (2 * e l)) * P l * μ + ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax) * 1
          by ring]
      exact this.congr_fun (fun N => by beta_reduce; ring)
    have := (H1.mul_left α).sub (hasSum_sum hl)
    rw [mul_comm μ α]
    refine this.congr_fun (fun N => ?_)
    beta_reduce
    rw [hEG N, mul_sub]
    congr 1
    · ring
    · rw [mul_sum]
  -- closed forms of the moments
  have hαv : μ * α = T * (r ⬝ᵥ x) := by
    rw [hμ, irt_sp_omega_lin lam x hlam r T]; rfl
  have hPv : ∀ l, μ * P l = e l := by
    intro l
    rw [hμ]; simp only [P, φ]
    rw [irt_sp_omega_lin lam x hlam (fun j => A l j) T]
    simp [hedef, mulVec, dotProduct]
  have hQv : ∀ l, μ * Q l ≤ T * Wv l := by
    intro l
    have e1 : μ * Q l = T * ∑ j, A l j * A l j * x j := by
      rw [hμ]; simp only [Q, φ]
      simp_rw [irt_sp_phi_sq (fun j => A l j)]
      rw [irt_sp_omega_lin lam x hlam (fun j => A l j * A l j) T]
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ hT.le
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hxl j)
      (mul_nonneg (hA l j) (hA l j))
  -- the lower bound on SPA
  have hlow : μ * α - ∑ l, ((ρ / (2 * s)) * (μ * Q l + μ ^ 2 * P l ^ 2) +
        (-(ρ / (2 * s)) * (2 * e l)) * (μ * P l) + ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax)) ≤
      irtValue A r lam sel 0 T C := by
    rw [hspa, ← hHS.tsum_eq]
    refine Summable.tsum_le_tsum (fun N => mul_le_mul_of_nonneg_left
      (irt_sp_ex_mono lam p hlam hp0 hp1 N _ _ (hGle N)) (irt_sq_pmf_nonneg _ _)) hHS.summable ?_
    exact hsumm'
  have hterm : ∀ l, (ρ / (2 * s)) * (μ * Q l + μ ^ 2 * P l ^ 2) +
      (-(ρ / (2 * s)) * (2 * e l)) * (μ * P l) + ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax) ≤
      s * (ρ * (Wv l / 2 + 1 / 2 + Amax)) := by
    intro l
    have h1 : μ ^ 2 * P l ^ 2 = e l ^ 2 := by rw [← hPv l]; ring
    rw [h1, hPv l]
    have h2 : (ρ / (2 * s)) * (μ * Q l) ≤ (ρ / (2 * s)) * (T * Wv l) :=
      mul_le_mul_of_nonneg_left (hQv l) (by positivity)
    have h3 : (ρ / (2 * s)) * (T * Wv l) = s * (ρ * (Wv l / 2)) := by
      rw [← hss]; field_simp
    have h4 : ρ * Amax ≤ s * (ρ * Amax) := by nlinarith [mul_nonneg hρ0 hAmax0]
    have h5 : (ρ / (2 * s)) * (μ * Q l + e l ^ 2) + (-(ρ / (2 * s)) * (2 * e l)) * e l +
        ρ * (e l ^ 2 / (2 * s) + s / 2 + Amax) =
        (ρ / (2 * s)) * (μ * Q l) + ρ * (s / 2) + ρ * Amax := by
      field_simp; ring
    rw [h5]
    nlinarith
  have hfin := sum_le_sum fun l (_ : l ∈ univ) => hterm l
  rw [← mul_sum] at hfin
  rw [hdlp]
  have : s * (r ⬝ᵥ lam) ≥ 0 := mul_nonneg hs0.le hrl0
  nlinarith
