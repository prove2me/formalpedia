-- Prove2me | solution 1 for SecSampling.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T10:21:59.84895+00:00
-- url     : https://prove2.me/submissions/b3dee401-6535-4fc1-99e5-ddfe79c25d13

import Mathlib
import Definitions.Def_SecSampling_ColoredLastZero
import Theorems.Thm_SecSampling_proposition_4

namespace SecSampling.T4

open Finset

noncomputable def beta (p : ℝ) (L b : ℕ) : ℝ := (L.choose b : ℝ) * p ^ b * (1 - p) ^ (L - b)

lemma mem_strings {n : ℕ} {I : List Bool} : I ∈ strings n ↔ I.length = n := by
  unfold strings
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, rfl⟩; simp
  · rintro rfl; exact ⟨I.get, List.ofFn_get I⟩

lemma sum_strings_append (m L : ℕ) (f : List Bool → ℝ) :
    ∑ I ∈ strings (m + L), f I = ∑ R ∈ strings m, ∑ B ∈ strings L, f (R ++ B) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun I => (I.take m, I.drop m)) (fun x => x.1 ++ x.2) ?_ ?_ ?_ ?_ ?_
  · intro I hI
    rw [mem_strings] at hI
    simp only [Finset.mem_product, mem_strings, List.length_take, List.length_drop]
    omega
  · rintro ⟨R, B⟩ h
    simp only [Finset.mem_product, mem_strings] at h
    simp only [mem_strings, List.length_append]
    omega
  · intro I _; simp
  · rintro ⟨R, B⟩ h
    simp only [Finset.mem_product, mem_strings] at h
    simp [← h.1]
  · intro I _; simp

lemma weight_append (p : ℝ) (R B : List Bool) : weight p (R ++ B) = weight p R * weight p B := by
  unfold weight bitNorm
  rw [List.count_append, List.length_append]
  have h1 := List.count_le_length (a := true) (l := R)
  have h2 := List.count_le_length (a := true) (l := B)
  rw [show R.length + B.length - (R.count true + B.count true)
      = (R.length - R.count true) + (B.length - B.count true) by omega]
  rw [pow_add, pow_add]; ring

lemma lastZero_le (I : List Bool) : lastZero I ≤ I.length := by
  unfold lastZero; split_ifs <;> omega

lemma perfColored_eq (p : ℝ) (Q : ColStrategy) (m L : ℕ) :
    perfColored p Q m (m + L) = ∑ B ∈ strings L,
      weight p B * perfLZ p (fun r h => Q (m + L) r (bitNorm B) h) m := by
  unfold perfColored
  rw [sum_strings_append, Finset.sum_comm]
  unfold perfLZ
  refine Finset.sum_congr rfl (fun B hB => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun R hR => ?_)
  rw [mem_strings] at hR hB
  have hlz := lastZero_le R
  have htake : (R ++ B).take m = R := by rw [← hR]; simp
  have hdrop : (R ++ B).drop m = B := by rw [← hR]; simp
  have hlen : (R ++ B).length = m + L := by simp [hR, hB]
  have htj : ∀ j, j ≤ R.length → (R ++ B).take j = R.take j := fun j hj =>
    List.take_append_of_le_length hj
  rw [weight_append]
  unfold winColored winLZ stopProbAt
  rw [htake, hdrop, hlen]
  split_ifs with h
  · rw [htj _ hlz]
    have : ∏ j ∈ Finset.Ico 1 (lastZero R), (1 - Q (m + L) (bitNorm R) (bitNorm B) ((R ++ B).take j))
        = ∏ j ∈ Finset.Ico 1 (lastZero R), (1 - Q (m + L) (bitNorm R) (bitNorm B) (R.take j)) := by
      refine Finset.prod_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Ico] at hj
      rw [htj j (by omega)]
    rw [this]; ring
  · ring

lemma strings_one : strings 1 = {[false], [true]} := by decide

lemma beta_succ_succ (p : ℝ) (L b : ℕ) :
    beta p (L + 1) (b + 1) = p * beta p L b + (1 - p) * beta p L (b + 1) := by
  unfold beta
  rw [Nat.choose_succ_succ', Nat.cast_add]
  rcases lt_or_ge b L with h | h
  · rw [show L + 1 - (b + 1) = L - b by omega, show L - b = (L - (b + 1)) + 1 by omega]
    ring
  · rw [Nat.choose_eq_zero_of_lt (show L < b + 1 by omega)]
    rw [show L + 1 - (b + 1) = L - b by omega]
    ring

lemma beta_zero_succ (p : ℝ) (L : ℕ) : beta p (L + 1) 0 = (1 - p) * beta p L 0 := by
  unfold beta; simp; ring

lemma beta_over (p : ℝ) (L : ℕ) : beta p L (L + 1) = 0 := by
  unfold beta; simp

lemma E_succ (p : ℝ) (L : ℕ) (g : ℕ → ℝ) :
    ∑ b ∈ range (L + 1), beta p L b * ((1 - p) * g b + p * g (b + 1))
      = ∑ b ∈ range (L + 2), beta p (L + 1) b * g b := by
  rw [Finset.sum_range_succ' _ (L + 1)]
  simp_rw [beta_succ_succ, beta_zero_succ]
  have h2 : ∑ b ∈ range (L + 1), (1 - p) * beta p L (b + 1) * g (b + 1)
      = ∑ b ∈ range (L + 1), beta p L b * ((1 - p) * g b) - (1 - p) * beta p L 0 * g 0 := by
    rw [Finset.sum_range_succ _ L, beta_over, Finset.sum_range_succ' _ L]
    ring_nf
  have : ∀ b, (p * beta p L b + (1 - p) * beta p L (b + 1)) * g (b + 1)
      = beta p L b * (p * g (b + 1)) + (1 - p) * beta p L (b + 1) * g (b + 1) := fun b => by ring
  simp_rw [this, Finset.sum_add_distrib, h2, mul_add, Finset.sum_add_distrib]
  ring

lemma sum_strings_bitNorm (p : ℝ) (L : ℕ) (g : ℕ → ℝ) :
    ∑ B ∈ strings L, weight p B * g (bitNorm B) = ∑ b ∈ range (L + 1), beta p L b * g b := by
  induction L generalizing g with
  | zero =>
    have : strings 0 = {[]} := by decide
    simp [this, weight, bitNorm, beta]
  | succ L ih =>
    rw [sum_strings_append L 1, strings_one]
    have : ∀ R : List Bool, ∑ B ∈ ({[false], [true]} : Finset (List Bool)),
        weight p (R ++ B) * g (bitNorm (R ++ B))
        = weight p R * ((1 - p) * g (bitNorm R) + p * g (bitNorm R + 1)) := by
      intro R
      rw [Finset.sum_pair (by decide), weight_append, weight_append]
      simp [weight, bitNorm, List.count_append]
      ring_nf
    simp_rw [this]
    rw [ih (fun b => (1 - p) * g b + p * g (b + 1))]
    exact E_succ p L g

lemma beta_sum (p : ℝ) (L : ℕ) : ∑ b ∈ range (L + 1), beta p L b = 1 := by
  have := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum ℝ L)
  simpa [Polynomial.eval_finsetSum, bernsteinPolynomial, beta] using this

lemma beta_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (L b : ℕ) : 0 ≤ beta p L b := by
  unfold beta; have : 0 ≤ 1 - p := by linarith
  positivity

lemma beta_diff (p : ℝ) (L b : ℕ) (hb : b ≤ L + 1) :
    (beta p (L + 1) b - beta p L b) * ((L + 1) * (1 - p))
      = beta p (L + 1) b * (b - (L + 1) * p) := by
  have hc := Nat.choose_mul_succ_eq L b
  have hc' : (L.choose b : ℝ) * (L + 1) = ((L + 1).choose b : ℝ) * ((L + 1 : ℝ) - b) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hc
    push_cast [Nat.cast_sub hb] at this
    linarith
  unfold beta
  rcases lt_or_ge b (L + 1) with h | h
  · rw [show L + 1 - b = (L - b) + 1 by omega, pow_succ]
    linear_combination (-(p ^ b * (1 - p) ^ (L - b) * (1 - p))) * hc'
  · have hbL : b = L + 1 := by omega
    subst hbL
    simp
    left; ring

lemma beta_var (p : ℝ) (L : ℕ) :
    ∑ b ∈ range (L + 1), beta p L b * ((b : ℝ) - L * p) ^ 2 = L * p * (1 - p) := by
  have := congrArg (Polynomial.eval p) (bernsteinPolynomial.variance ℝ L)
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, bernsteinPolynomial, nsmul_eq_mul] at this
  rw [← this]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  unfold beta; ring

/-- one-step total-variation bound -/
lemma tv_step {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (L : ℕ) (g : ℕ → ℝ)
    (hg : ∀ b, |g b| ≤ 1) (t : ℝ) (ht : 0 < t) :
    |∑ b ∈ range (L + 2), beta p (L + 1) b * g b - ∑ b ∈ range (L + 1), beta p L b * g b|
      ≤ (p / t + t / ((L + 1) * (1 - p))) / 2 := by
  have hq : 0 < 1 - p := by linarith
  set c : ℝ := (L + 1) * (1 - p) with hcdef
  have hc : 0 < c := by positivity
  have hsplit : ∑ b ∈ range (L + 2), beta p (L + 1) b * g b - ∑ b ∈ range (L + 1), beta p L b * g b
      = ∑ b ∈ range (L + 2), beta p (L + 1) b * ((b : ℝ) - (L + 1) * p) / c * g b := by
    rw [show ∑ b ∈ range (L + 1), beta p L b * g b = ∑ b ∈ range (L + 2), beta p L b * g b by
      rw [Finset.sum_range_succ _ (L + 1), beta_over]; ring]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [Finset.mem_range] at hb
    rw [← beta_diff p L b (by omega)]
    field_simp
    ring
  rw [hsplit]
  have hβ : ∀ b, 0 ≤ beta p (L + 1) b := beta_nonneg hp0.le hp1.le (L + 1)
  have hpt : ∀ x : ℝ, |x| ≤ (x ^ 2 / t + t) / 2 := by
    intro x
    have : 0 ≤ (|x| - t) ^ 2 := sq_nonneg _
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    rw [div_add' _ _ _ ht.ne', div_div, le_div_iff₀ (mul_pos ht two_pos)]
    nlinarith
  calc |∑ b ∈ range (L + 2), beta p (L + 1) b * ((b : ℝ) - (L + 1) * p) / c * g b|
      ≤ ∑ b ∈ range (L + 2), |beta p (L + 1) b * ((b : ℝ) - (L + 1) * p) / c * g b| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ range (L + 2), beta p (L + 1) b * ((((b : ℝ) - (L + 1) * p) ^ 2 / t + t) / 2) / c := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (hβ b), abs_of_pos hc]
        have h1 := hpt ((b : ℝ) - (L + 1) * p)
        have h2 := hg b
        have h3 : 0 ≤ beta p (L + 1) b * |(b : ℝ) - (L + 1) * p| / c :=
          div_nonneg (mul_nonneg (hβ b) (abs_nonneg _)) hc.le
        calc beta p (L + 1) b * |(b : ℝ) - (L + 1) * p| / c * |g b|
            ≤ beta p (L + 1) b * |(b : ℝ) - (L + 1) * p| / c * 1 := mul_le_mul_of_nonneg_left h2 h3
          _ ≤ _ := by
            rw [mul_one]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (hβ b)) hc.le
    _ = ((∑ b ∈ range (L + 2), beta p (L + 1) b * ((b : ℝ) - (L + 1) * p) ^ 2) / t
          + t * ∑ b ∈ range (L + 2), beta p (L + 1) b) / (2 * c) := by
        rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        field_simp
    _ = (p / t + t / ((L + 1) * (1 - p))) / 2 := by
        have hv := beta_var p (L + 1)
        push_cast at hv
        rw [hv, beta_sum, hcdef]
        field_simp

lemma perfLZ_nonneg_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (q : LZStrategy) (hq : IsLZStrategy q)
    (n : ℕ) : 0 ≤ perfLZ p q n ∧ perfLZ p q n ≤ 1 := by
  have hq1 : 0 ≤ 1 - p := by linarith
  have hw : ∀ I, 0 ≤ weight p I := fun I => by unfold weight; positivity
  have hwin : ∀ I, 0 ≤ winLZ q I ∧ winLZ q I ≤ 1 := by
    intro I
    unfold winLZ stopProbAt
    split_ifs
    · have h0 : ∀ j, 0 ≤ 1 - q (bitNorm I) (I.take j) := fun j => by linarith [(hq (bitNorm I) (I.take j)).2]
      have h1 : ∀ j, 1 - q (bitNorm I) (I.take j) ≤ 1 := fun j => by linarith [(hq (bitNorm I) (I.take j)).1]
      have hP0 := Finset.prod_nonneg (fun j (_ : j ∈ Finset.Ico 1 (lastZero I)) => h0 j)
      have hP1 := Finset.prod_le_one (fun j (_ : j ∈ Finset.Ico 1 (lastZero I)) => h0 j)
        (fun j _ => h1 j)
      have := hq (bitNorm I) (I.take (lastZero I))
      constructor
      · exact mul_nonneg this.1 hP0
      · calc _ ≤ 1 * 1 := mul_le_mul this.2 hP1 hP0 zero_le_one
          _ = 1 := by ring
    · exact ⟨zero_le_one, le_rfl⟩
  have hsum : ∑ I ∈ strings n, weight p I = 1 := by
    have := sum_strings_bitNorm p n (fun _ => 1)
    simp only [mul_one] at this
    rw [this, beta_sum]
  unfold perfLZ
  constructor
  · exact Finset.sum_nonneg (fun I _ => mul_nonneg (hw I) (hwin I).1)
  · calc _ ≤ ∑ I ∈ strings n, weight p I :=
          Finset.sum_le_sum (fun I _ => by nlinarith [hw I, hwin I])
      _ = 1 := hsum

lemma one_le_lastZero {I : List Bool} (h : false ∈ I) : 1 ≤ lastZero I := by
  unfold lastZero
  rw [if_pos h]
  have := List.idxOf_lt_length_iff.2 (List.mem_reverse.2 h)
  rw [List.length_reverse] at this
  omega

/-- Kuhn-type mixing -/
lemma mixture {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (q : ι → LZStrategy) (hq : ∀ i, IsLZStrategy (q i)) :
    ∃ qb : LZStrategy, IsLZStrategy qb ∧ ∀ (p : ℝ) (m : ℕ),
      perfLZ p qb m = ∑ i ∈ s, w i * perfLZ p (q i) m := by
  classical
  set C : ι → ℕ → List Bool → ℝ := fun i r h =>
    ∏ j ∈ Finset.Ico 1 h.length, (1 - q i r (h.take j)) with hCdef
  set D : ℕ → List Bool → ℝ := fun r h => ∑ i ∈ s, w i * C i r h with hDdef
  set N : ℕ → List Bool → ℝ := fun r h => ∑ i ∈ s, w i * C i r h * q i r h with hNdef
  have hC0 : ∀ i r h, 0 ≤ C i r h := fun i r h =>
    Finset.prod_nonneg (fun j _ => by linarith [(hq i r (h.take j)).2])
  have hN0 : ∀ r h, 0 ≤ N r h := fun r h =>
    Finset.sum_nonneg (fun i hi => mul_nonneg (mul_nonneg (hw i hi) (hC0 i r h)) (hq i r h).1)
  have hND : ∀ r h, N r h ≤ D r h := fun r h =>
    Finset.sum_le_sum (fun i hi => by
      have := mul_nonneg (hw i hi) (hC0 i r h)
      nlinarith [(hq i r h).2])
  set qb : LZStrategy := fun r h => if D r h = 0 then 0 else N r h / D r h with hqbdef
  have hqbD : ∀ r h, qb r h * D r h = N r h := by
    intro r h
    simp only [hqbdef]
    split_ifs with h0
    · linarith [hN0 r h, hND r h]
    · field_simp
  have hCt : ∀ i r (I : List Bool) t, t ≤ I.length →
      C i r (I.take t) = ∏ j ∈ Finset.Ico 1 t, (1 - q i r (I.take j)) := by
    intro i r I t ht
    simp only [hCdef, List.length_take, min_eq_left ht]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_Ico] at hj
    rw [List.take_take, min_eq_left (by omega)]
  have key : ∀ r (I : List Bool) t, 1 ≤ t → t ≤ I.length →
      ∏ j ∈ Finset.Ico 1 t, (1 - qb r (I.take j)) = D r (I.take t) := by
    intro r I t h1 
    induction t, h1 using Nat.le_induction with
    | base =>
      intro _
      simp only [Finset.Ico_self, Finset.prod_empty, hDdef]
      rw [← hw1]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hCt i r I 1 (by omega)]
      simp
    | succ t ht ih =>
      intro hlen
      rw [Finset.prod_Ico_succ_top ht, ih (by omega)]
      have hDs : D r (I.take (t + 1)) = D r (I.take t) - N r (I.take t) := by
        simp only [hDdef, hNdef]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hCt i r I (t + 1) hlen, hCt i r I t (by omega), Finset.prod_Ico_succ_top ht]
        ring
      rw [hDs, mul_sub, mul_one, mul_comm, hqbD]
  have hwin : ∀ I, winLZ qb I = ∑ i ∈ s, w i * winLZ (q i) I := by
    intro I
    unfold winLZ
    split_ifs with h
    · have h1 := one_le_lastZero h
      have h2 := lastZero_le I
      unfold stopProbAt
      rw [key _ I _ h1 h2, hqbD]
      simp only [hNdef]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hCt i _ I _ h2]
      ring
    · simp [hw1]
  refine ⟨qb, ?_, ?_⟩
  · intro r h
    simp only [hqbdef]
    split_ifs with h0
    · exact ⟨le_rfl, zero_le_one⟩
    · have hD0 : 0 ≤ D r h := (hN0 r h).trans (hND r h)
      exact ⟨div_nonneg (hN0 r h) hD0, div_le_one_of_le₀ (hND r h) hD0⟩
  · intro p m
    unfold perfLZ
    simp_rw [hwin, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun I _ => by ring))

/-- uniform version of proposition 4 by compactness -/
lemma uniform_prop4 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ M, ∀ q : LZStrategy, IsLZStrategy q → ∃ m, N₀ ≤ m ∧ m ≤ M ∧
      perfLZ p q m < guarantee p + ε := by
  classical
  set K : Set LZStrategy :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1)) with hKdef
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hev : ∀ (a : ℕ) (b : List Bool), Continuous (fun q : LZStrategy => q a b) :=
    fun a b => (continuous_apply b).comp (continuous_apply a)
  have hcont : ∀ n, Continuous (fun q : LZStrategy => perfLZ p q n) := by
    intro n
    unfold perfLZ
    refine continuous_finsetSum _ (fun I _ => continuous_const.mul ?_)
    unfold winLZ stopProbAt
    by_cases h : false ∈ I
    · simp only [h, ↓reduceIte]
      exact (hev _ _).mul (continuous_finsetProd _ (fun j _ => continuous_const.sub (hev _ _)))
    · simp only [h, ↓reduceIte]
      exact continuous_const
  set U : ℕ → Set LZStrategy := fun k => {q | perfLZ p q (N₀ + k) < guarantee p + ε} with hUdef
  have hU : ∀ k, IsOpen (U k) := fun k => isOpen_lt (hcont _) continuous_const
  have hcov : K ⊆ ⋃ k, U k := by
    intro q hq
    have hq' : IsLZStrategy q := fun m h => by
      have := hq m trivial h trivial
      exact ⟨this.1, this.2⟩
    obtain ⟨n, hn, hlt⟩ := proposition_4 p hp0 hp1 q hq' ε hε N₀
    refine Set.mem_iUnion.2 ⟨n - N₀, ?_⟩
    show perfLZ p q (N₀ + (n - N₀)) < _
    rwa [Nat.add_sub_cancel' hn]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  refine ⟨N₀ + t.sup id, fun q hq => ?_⟩
  have hqK : q ∈ K := fun m _ h _ => hq m h
  obtain ⟨k, hk, hkU⟩ := Set.mem_iUnion₂.1 (ht hqK)
  have hle : k ≤ t.sup id := Finset.le_sup (f := id) hk
  exact ⟨N₀ + k, by omega, by omega, hkU⟩

noncomputable def E (p : ℝ) (K : ℕ) (g : ℕ → ℝ) : ℝ := ∑ b ∈ range (K + 1), beta p K b * g b

lemma tv_tele (p : ℝ) (L : ℕ) (g : ℕ → ℝ) (η : ℝ)
    (hη : ∀ K, L ≤ K → |E p (K + 1) g - E p K g| ≤ η) :
    ∀ j : ℕ, |E p (L + j) g - E p L g| ≤ j * η := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := hη (L + j) (by omega)
    rw [← add_assoc]
    calc |E p (L + j + 1) g - E p L g|
        = |(E p (L + j + 1) g - E p (L + j) g) + (E p (L + j) g - E p L g)| := by ring_nf
      _ ≤ |E p (L + j + 1) g - E p (L + j) g| + |E p (L + j) g - E p L g| := abs_add_le _ _
      _ ≤ η + j * η := add_le_add h1 ih
      _ = ((j + 1 : ℕ) : ℝ) * η := by push_cast; ring

end SecSampling.T4

open SecSampling SecSampling.T4 in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (Q : ColStrategy) (hQ : IsColStrategy Q)
    (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ m n : ℕ, N₀ ≤ m ∧ m ≤ n ∧ perfColored p Q m n < guarantee p + ε := by
  obtain ⟨M, hM⟩ := uniform_prop4 p hp0 hp1 (ε / 2) (by linarith) N₀
  set η : ℝ := ε / (2 * (M + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hq1 : 0 < 1 - p := by linarith
  obtain ⟨L, hL⟩ := exists_nat_gt (1 / (η ^ 2 * (1 - p)))
  set n := M + L with hn
  have hstrat : ∀ b, IsLZStrategy (fun r h => Q n r b h) := fun b r h => hQ n r b h
  obtain ⟨qb, hqb, hqbperf⟩ := mixture (Finset.range (L + 1)) (beta p L)
    (fun b _ => beta_nonneg hp0.le hp1.le L b) (beta_sum p L) (fun b => fun r h => Q n r b h) hstrat
  obtain ⟨m, hm0, hmM, hm⟩ := hM qb hqb
  refine ⟨m, n, hm0, by omega, ?_⟩
  set g : ℕ → ℝ := fun b => perfLZ p (fun r h => Q n r b h) m with hg
  have hgb : ∀ b, |g b| ≤ 1 := by
    intro b
    obtain ⟨h1, h2⟩ := perfLZ_nonneg_le hp0 hp1 _ (hstrat b) m
    rw [abs_le]; constructor <;> linarith
  have hstep : ∀ K, L ≤ K → |E p (K + 1) g - E p K g| ≤ η := by
    intro K hK
    have := tv_step hp0 hp1 K g hgb (1 / η) (by positivity)
    unfold E
    refine this.trans ?_
    have hK' : (L : ℝ) ≤ K := by exact_mod_cast hK
    have h1 : p / (1 / η) ≤ η := by
      rw [div_div_eq_mul_div, div_one]; nlinarith
    have h2 : 1 / η / ((K + 1) * (1 - p)) ≤ η := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 / (η ^ 2 * (1 - p)) < K + 1 := by linarith
      rw [div_lt_iff₀ (by positivity)] at this
      rw [div_le_iff₀ hη]
      nlinarith
    linarith
  have htele := tv_tele p L g η hstep (M - m)
  have hdecomp : perfColored p Q m n = E p (L + (M - m)) g := by
    have : n = m + (L + (M - m)) := by omega
    rw [this, perfColored_eq, E]
    rw [← this]
    exact sum_strings_bitNorm p (L + (M - m)) g
  have hmix : perfLZ p qb m = E p L g := by
    rw [hqbperf]; rfl
  have hMm : ((M - m : ℕ) : ℝ) * η ≤ ε / 2 := by
    have : ((M - m : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M m
    calc ((M - m : ℕ) : ℝ) * η ≤ M * η := by gcongr
      _ ≤ ε / 2 := by
        rw [hηdef, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  rw [hdecomp]
  have := (abs_le.mp htele).2
  linarith
