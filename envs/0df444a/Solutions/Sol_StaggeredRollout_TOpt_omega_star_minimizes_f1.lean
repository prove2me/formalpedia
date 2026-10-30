-- Prove2me | solution 1 for StaggeredRollout.TOpt.omega_star_minimizes_f1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:49:28.459363+00:00
-- url     : https://prove2.me/submissions/0afbf38e-9450-4af5-8f36-49ed333907ea

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Setting
import Definitions.Def_StaggeredRollout_TOpt_Quadratic
import Theorems.Thm_StaggeredRollout_TOpt_a_ell_feasible

open Matrix StaggeredRollout.TOpt

namespace AellAux

lemma rho_range (n r : ℕ) (hr : r ≤ n) :
    ∑ c ∈ Finset.range n, ((n : ℝ) - ((max r c : ℕ) : ℝ))
      = ((n : ℝ) - r) * ((n : ℝ) + r + 1) / 2 := by
  induction n generalizing r with
  | zero =>
    have : r = 0 := by omega
    subst this; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge n r with h | h
    · have hr' : r = n + 1 := by omega
      subst hr'
      have : ∀ c ∈ Finset.range n, ((↑(n + 1) : ℝ) - ((max (n + 1) c : ℕ) : ℝ)) = 0 := by
        intro c hc
        rw [Finset.mem_range] at hc
        rw [max_eq_left (by omega)]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero, max_eq_left (by omega)]
      push_cast; ring
    · have e : ∀ c ∈ Finset.range n, ((↑(n + 1) : ℝ) - ((max r c : ℕ) : ℝ))
          = ((n : ℝ) - ((max r c : ℕ) : ℝ)) + 1 := by
        intro c _; push_cast; ring
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih r h, max_eq_right h]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast; ring

lemma rho_fin (K r : ℕ) (hr : r ≤ K) :
    ∑ c : Fin K, ((K : ℝ) - ((max r c.val : ℕ) : ℝ))
      = ((K : ℝ) - r) * ((K : ℝ) + r + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun c => ((K : ℝ) - ((max r c : ℕ) : ℝ))) K]
  exact rho_range K r hr

lemma icc_sum (m : ℕ) (x : ℝ) :
    ∑ l ∈ Finset.Icc 1 m, (x - (l : ℝ)) = m * x - (m : ℝ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast; ring

lemma comparison {K : ℕ} (M : Matrix (Fin K) (Fin K) ℝ)
    (hoff : ∀ r c, r ≠ c → M r c ≤ 0) (hrow : ∀ r, 0 < ∑ c, M r c)
    (x : Fin K → ℝ) (hx : ∀ r, 0 ≤ (M *ᵥ x) r) : ∀ r, 0 ≤ x r := by
  by_contra hneg
  simp only [not_forall, not_le] at hneg
  obtain ⟨r0, hr0⟩ := hneg
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ x ⟨r0, Finset.mem_univ _⟩
  have hxm : x m < 0 := lt_of_le_of_lt (hm r0 (Finset.mem_univ _)) hr0
  have h1 : (M *ᵥ x) m ≤ x m * ∑ c, M m c := by
    simp only [mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    by_cases hc : m = c
    · subst hc; rw [mul_comm]
    · have h3 := hoff m c hc
      have h4 := hm c (Finset.mem_univ _)
      nlinarith
  have h2 : x m * ∑ c, M m c < 0 := mul_neg_of_neg_of_pos hxm (hrow m)
  linarith [hx m]

lemma fin_mono {K : ℕ} (f : Fin K → ℝ)
    (h : ∀ (i : ℕ) (hi : i + 1 < K), f ⟨i, by omega⟩ ≤ f ⟨i + 1, hi⟩) : Monotone f := by
  have key : ∀ n a (ha : a < K) (hb : a + n < K), f ⟨a, ha⟩ ≤ f ⟨a + n, hb⟩ := by
    intro n
    induction n with
    | zero => intro a ha hb; exact le_rfl
    | succ n ih =>
      intro a ha hb
      exact le_trans (ih a ha (by omega)) (h (a + n) (by omega))
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have hab' : a ≤ b := hab
  have := key (b - a) a ha (by omega)
  have e : a + (b - a) = b := by omega
  simp only [e] at this
  exact this

noncomputable def Lb (u : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then -1 else if k = 1 then -1 else if k = 2 then -1 + u else if k = 3 then 1 - u else 1

noncomputable def Ub (u : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then -1 else if k = 1 then -1 + u else if k = 2 then 1 - u else 1

def stg (ℓ T : ℕ) (t : Fin T) : ℕ :=
  if t.val + 1 ≤ ℓ / 2 then 0 else if t.val + 1 ≤ ℓ then 1 else if t.val + 1 ≤ T - ℓ then 2
  else if t.val + 1 ≤ T - ℓ / 2 then 3 else 4

lemma omega_part (ℓ T : ℕ) (h2T : 2 * ℓ < T) (hd1 : (ℓ : ℝ) + 1 ≤ (T : ℝ) - ℓ)
    (hab : ∀ r, -1 ≤ avec ℓ T r ∧ avec ℓ T r ≤ -1 + ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ))
    (hamono : Monotone (avec ℓ T)) :
    Monotone (omegaStar ℓ T) ∧ (∀ t, -1 ≤ omegaStar ℓ T t ∧ omegaStar ℓ T t ≤ 1) := by
  have hdpos : (0 : ℝ) < (T : ℝ) - ℓ := by
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    linarith
  have hA2 : ∀ i j : Fin (ℓ - ℓ / 2), i.val ≤ j.val → avec ℓ T i ≤ avec ℓ T j :=
    fun i j hij => hamono hij
  have hu0 : 0 ≤ ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) := by positivity
  have hu1 : ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) ≤ 1 := by rw [div_le_one hdpos]; exact hd1
  have hst5 : ∀ t, stg ℓ T t < 5 := by
    intro t; unfold stg; split_ifs <;> omega
  have hstmono : Monotone (stg ℓ T) := by
    intro t t' htt
    have : t.val ≤ t'.val := htt
    unfold stg; split_ifs <;> omega
  have hLU : ∀ k k', k < k' → k' < 5 →
      Ub (((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ)) k ≤ Lb (((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ)) k' := by
    intro k k' hk hk'
    unfold Lb Ub
    split_ifs <;> first | omega | linarith
  have hbnd : ∀ t, Lb (((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ)) (stg ℓ T t) ≤ omegaStar ℓ T t ∧
      omegaStar ℓ T t ≤ Ub (((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ)) (stg ℓ T t) := by
    intro t
    have ht := t.isLt
    set u := ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) with hu
    have hL1 : Lb u 1 = -1 := by simp [Lb]
    have hU1 : Ub u 1 = -1 + u := by simp [Ub]
    have hL2 : Lb u 2 = -1 + u := by simp [Lb]
    have hU2 : Ub u 2 = 1 - u := by simp [Ub]
    have hL3 : Lb u 3 = 1 - u := by simp [Lb]
    have hU3 : Ub u 3 = 1 := by simp [Ub]
    unfold stg omegaStar
    split_ifs with h1 h2 h3 h4
    · simp [Lb, Ub]
    · rw [hL1, hU1]
      exact hab _
    · rw [hL2, hU2]
      have h3' : ((t.val : ℕ) : ℝ) + 1 ≤ (T : ℝ) - ℓ := by
        have : t.val + 1 + ℓ ≤ T := by omega
        have : ((t.val + 1 + ℓ : ℕ) : ℝ) ≤ T := by exact_mod_cast this
        push_cast at this; linarith
      have h2' : (ℓ : ℝ) + 1 ≤ ((t.val : ℕ) : ℝ) + 1 := by
        have : ℓ ≤ t.val := by omega
        have : (ℓ : ℝ) ≤ t.val := by exact_mod_cast this
        linarith
      constructor
      · rw [hu]
        have : ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) ≤ (2 * (((t.val : ℕ) : ℝ) + 1) - ((ℓ : ℝ) + 1)) / ((T : ℝ) - ℓ) := by
          rw [div_le_div_iff_of_pos_right hdpos]; linarith
        linarith
      · rw [hu]
        have : (2 * (((t.val : ℕ) : ℝ) + 1) - ((ℓ : ℝ) + 1)) / ((T : ℝ) - ℓ) + ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) ≤ 2 := by
          rw [← add_div, div_le_iff₀ hdpos]; linarith
        linarith
    · rw [hL3, hU3]
      have := hab ⟨T - (t.val + 1) - ℓ / 2, by omega⟩
      constructor <;> linarith [this.1, this.2]
    · simp [Lb, Ub]
  refine ⟨?_, ?_⟩
  · intro t t' htt
    have htt' : t.val ≤ t'.val := htt
    by_cases heq : stg ℓ T t = stg ℓ T t'
    · unfold stg at heq
      unfold omegaStar
      split_ifs at heq ⊢ <;> (try omega) <;> (try norm_num)
      · exact hA2 _ _ (by dsimp only; omega)
      · apply div_le_div_of_nonneg_right _ hdpos.le
        have : ((t.val : ℕ) : ℝ) ≤ ((t'.val : ℕ) : ℝ) := by exact_mod_cast htt'
        linarith
      · exact hA2 _ _ (by dsimp only; omega)
    · have hlt : stg ℓ T t < stg ℓ T t' := lt_of_le_of_ne (hstmono htt) heq
      have := hLU _ _ hlt (hst5 t')
      linarith [(hbnd t).2, (hbnd t').1]
  · intro t
    have h1 := hbnd t
    constructor
    · have : -1 ≤ Lb (((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ)) (stg ℓ T t) := by
        unfold Lb; split_ifs <;> linarith
      linarith [h1.1]
    · have : Ub (((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ)) (stg ℓ T t) ≤ 1 := by
        unfold Ub; split_ifs <;> linarith
      linarith [h1.2]



lemma src_cast (m : ℕ) : ∑ i ∈ Finset.range m, (i : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma rho2_range (n r : ℕ) (hr : r ≤ n) :
    ∑ c ∈ Finset.range n, ((n : ℝ) - ((max r c : ℕ) : ℝ)) * ((c : ℝ) + 1)
      = ((n : ℝ) - r) * (3 * r * (r + 1) + ((n : ℝ) - r + 1) * (n + 2 + 2 * r)) / 6 := by
  induction n generalizing r with
  | zero =>
    have : r = 0 := by omega
    subst this; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge n r with h | h
    · have hr' : r = n + 1 := by omega
      subst hr'
      have : ∀ c ∈ Finset.range n,
          ((↑(n + 1) : ℝ) - ((max (n + 1) c : ℕ) : ℝ)) * ((c : ℝ) + 1) = 0 := by
        intro c hc
        rw [Finset.mem_range] at hc
        rw [max_eq_left (by omega)]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero, max_eq_left (by omega)]
      push_cast; ring
    · have e : ∀ c ∈ Finset.range n, ((↑(n + 1) : ℝ) - ((max r c : ℕ) : ℝ)) * ((c : ℝ) + 1)
          = ((n : ℝ) - ((max r c : ℕ) : ℝ)) * ((c : ℝ) + 1) + ((c : ℝ) + 1) := by
        intro c _; push_cast; ring
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih r h, max_eq_right h,
        Finset.sum_add_distrib]
      rw [src_cast n]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast; ring

end AellAux

namespace AellAux

lemma poly_even (q r d : ℝ) (hr0 : 0 ≤ r) (hrK : r + 1 ≤ q)
    (hdT : (2 * q) ^ 3 + 5 * (2 * q) ^ 2 + 7 * (2 * q) + 3 < 8 * (2 * q) * d) :
    0 ≤ d * (q + r + 1) * ((2 * q + 1) * (r + 1) - (q + 1) * (q + r + 1 - q + r))
      - (2 * q + 1) * ((q - r) * (3 * r * (r + 1) + (q - r + 1) * (q + 2 + 2 * r)) / 6) := by
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hB : r ^ 2 + (q + 3) * r + (q + 1) * (q + 2) ≤ (q + 1) * (q + 2 + 2 * r) := by nlinarith
  have h4d : (2 * q + 1) * (q + 1) ≤ 4 * d := by nlinarith
  have hrat : 2 * (q + 2 + 2 * r) ≤ 3 * (q + 1 + r) := by linarith
  have hX : (2 * q + 1) * (r ^ 2 + (q + 3) * r + (q + 1) * (q + 2)) ≤ 6 * d * (q + r + 1) := by
    have hp : (0 : ℝ) ≤ 2 * q + 1 := by linarith
    have hp2 : (0 : ℝ) ≤ q + 1 + r := by linarith
    have s1 := mul_le_mul_of_nonneg_left hB hp
    have hpq : (0 : ℝ) ≤ (2 * q + 1) * (q + 1) := by nlinarith
    have s2 := mul_le_mul_of_nonneg_left hrat hpq
    have s3 := mul_le_mul_of_nonneg_right h4d hp2
    nlinarith
  have e : d * (q + r + 1) * ((2 * q + 1) * (r + 1) - (q + 1) * (q + r + 1 - q + r))
      - (2 * q + 1) * ((q - r) * (3 * r * (r + 1) + (q - r + 1) * (q + 2 + 2 * r)) / 6)
      = (q - r) * (6 * d * (q + r + 1) - (2 * q + 1) * (r ^ 2 + (q + 3) * r + (q + 1) * (q + 2))) / 6 := by
    ring
  rw [e]
  apply div_nonneg _ (by norm_num)
  apply mul_nonneg (by linarith)
  linarith

lemma poly_odd (q r d : ℝ) (hq0 : 0 ≤ q) (hqq : q = 0 ∨ 1 ≤ q) (hr0 : 0 ≤ r) (hrK : r + 1 ≤ q + 1)
    (hdT : (2 * q + 1) ^ 3 + 5 * (2 * q + 1) ^ 2 + 7 * (2 * q + 1) + 3 < 8 * (2 * q + 1) * d) :
    0 ≤ d * (q + r + 1) * ((2 * q + 1 + 1) * (r + 1) - (q + 1 + 1) * (q + r + 1 - (q + 1) + r))
      - (2 * q + 1 + 1) * (((q + 1) - r) * (3 * r * (r + 1) + ((q + 1) - r + 1) * ((q + 1) + 2 + 2 * r)) / 6) := by
  have hrq : r ≤ q := by linarith
  have hB : r ^ 2 + (q + 4) * r + (q + 2) * (q + 3) ≤ (q + 2) * (2 * r + q + 3) := by nlinarith
  have hd2 : (q + 1) ^ 2 * (q + 2) ≤ (2 * q + 1) * d := by nlinarith
  have hrat : (2 * q + 1) * (q + 3 + 2 * r) ≤ (3 * q + 3) * (q + 1 + r) := by
    rcases hqq with h0 | h1
    · have : r = 0 := by linarith
      subst h0; subst this; norm_num
    · nlinarith
  have hX : (2 * q + 2) * (r ^ 2 + (q + 4) * r + (q + 2) * (q + 3)) ≤ 12 * d * (q + r + 1) := by
    have hp : (0 : ℝ) < 2 * q + 1 := by linarith
    have hp2 : (0 : ℝ) ≤ q + 1 + r := by linarith
    have h22 : (0 : ℝ) ≤ 2 * q + 2 := by linarith
    have s1 := mul_le_mul_of_nonneg_left hB h22
    have hpq : (0 : ℝ) ≤ (2 * q + 2) * (q + 2) := by nlinarith
    have s2 := mul_le_mul_of_nonneg_left hrat hpq
    have s3 := mul_le_mul_of_nonneg_right hd2 hp2
    have s4 : (2 * q + 1) * ((2 * q + 2) * (r ^ 2 + (q + 4) * r + (q + 2) * (q + 3)))
        ≤ (2 * q + 1) * (12 * d * (q + r + 1)) := by nlinarith
    exact le_of_mul_le_mul_left s4 hp
  have e : d * (q + r + 1) * ((2 * q + 1 + 1) * (r + 1) - (q + 1 + 1) * (q + r + 1 - (q + 1) + r))
      - (2 * q + 1 + 1) * (((q + 1) - r) * (3 * r * (r + 1) + ((q + 1) - r + 1) * ((q + 1) + 2 + 2 * r)) / 6)
      = (q + 1 - r) * (12 * d * (q + r + 1) - (2 * q + 2) * (r ^ 2 + (q + 4) * r + (q + 2) * (q + 3))) / 6 := by
    ring
  rw [e]
  apply div_nonneg _ (by norm_num)
  apply mul_nonneg (by linarith)
  linarith

theorem cu_bound (ℓ T : ℕ) (hℓ : 0 < ℓ)
    (hT : ((ℓ : ℝ) ^ 3 + 13 * (ℓ : ℝ) ^ 2 + 7 * (ℓ : ℝ) + 3) / (8 * (ℓ : ℝ)) < (T : ℝ))  :
    ∀ c (hc : c < ℓ - ℓ / 2), avec ℓ T ⟨c, hc⟩ + 1
      ≤ ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) * ((c : ℝ) + 1) / (((ℓ - ℓ / 2 : ℕ) : ℝ) + 1) := by
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have h2T : 2 * ℓ < T := by
    have h8 : (0 : ℝ) < 8 * ℓ := by positivity
    rw [div_lt_iff₀ h8] at hT
    have : (2 * ℓ : ℝ) < T := by nlinarith [sq_nonneg ((ℓ : ℝ) - 3 / 2)]
    exact_mod_cast this
  have hd1 : (ℓ : ℝ) + 1 ≤ (T : ℝ) - ℓ := by
    have : ((2 * ℓ + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast h2T
    push_cast at this; linarith
  set d : ℝ := (T : ℝ) - ℓ with hd
  have hdpos : 0 < d := by linarith
  set h := ℓ / 2 with hh
  set K := ℓ - ℓ / 2 with hK
  have hKpos : 0 < K := by omega
  have hKh : K ≤ h + 1 := by omega
  have hhK : h ≤ K := by omega
  have hKl : K ≤ ℓ := by omega
  -- notation
  have hKh' : (K : ℝ) + h = ℓ := by
    have : K + h = ℓ := by omega
    exact_mod_cast this
  have h2h : (ℓ : ℝ) ≤ 2 * h + 1 := by
    have : ℓ ≤ 2 * h + 1 := by omega
    exact_mod_cast this
  have hKhr : (K : ℝ) ≤ h + 1 := by exact_mod_cast hKh
  set M := Mmat ℓ T with hMdef
  set E : Fin K → Fin K → ℝ := fun r c => (K : ℝ) - ((max r.val c.val : ℕ) : ℝ) with hEdef
  set tt : Fin K → ℝ := fun r => (h : ℝ) + r.val + 1 with htt
  have hM : ∀ r c, M r c = (if r = c then tt r else 0) - E r c / d := fun r c => rfl
  have hE1 : ∀ r c, 1 ≤ E r c := by
    intro r c
    have : (max r.val c.val) + 1 ≤ K := by have := r.isLt; have := c.isLt; omega
    have : ((max r.val c.val : ℕ) : ℝ) + 1 ≤ K := by exact_mod_cast this
    simp only [hEdef]; linarith
  have hrho : ∀ r : Fin K, ∑ c, E r c = ((K : ℝ) - r.val) * ((K : ℝ) + r.val + 1) / 2 :=
    fun r => rho_fin K r.val r.isLt.le
  have httge : ∀ r : Fin K, (K : ℝ) + r.val ≤ tt r := by intro r; simp only [htt]; linarith
  have hmulVec : ∀ x : Fin K → ℝ, ∀ r, (M *ᵥ x) r = tt r * x r - (∑ c, E r c * x c) / d := by
    intro x r
    simp only [mulVec, dotProduct, hM, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hoff : ∀ r c, r ≠ c → M r c ≤ 0 := by
    intro r c hrc
    rw [hM, if_neg hrc]
    have := hE1 r c
    have : 0 ≤ E r c / d := div_nonneg (by linarith) hdpos.le
    linarith
  have hrow : ∀ r, 0 < ∑ c, M r c := by
    intro r
    have h1 := hmulVec (fun _ => 1) r
    simp only [mulVec, dotProduct, mul_one] at h1
    rw [h1, hrho r]
    have hr : (r.val : ℝ) + 1 ≤ K := by
      have := r.isLt; exact_mod_cast this
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
    have hr0 : (0 : ℝ) ≤ r.val := Nat.cast_nonneg _
    have key : ((K : ℝ) - r.val) * ((K : ℝ) + r.val + 1) / 2 < tt r * d := by
      have := httge r
      nlinarith
    rw [sub_pos, div_lt_iff₀ hdpos]; linarith
  -- invertibility
  have hdet : M.det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff).mpr hdet
    apply hv0
    funext r
    have h1 := comparison M hoff hrow v (by intro r; rw [hv]; simp) r
    have h2 := comparison M hoff hrow (-v) (by intro r; rw [mulVec_neg, hv]; simp) r
    simp at h2
    simp; linarith
  have hMa : M *ᵥ avec ℓ T = bvec ℓ T := by
    simp only [avec, hMdef]
    rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hdet), one_mulVec]
  -- closed form of `b`
  have hb : ∀ r : Fin K, bvec ℓ T r = -tt r + tt r ^ 2 / d
      - (1 / d) * (((K : ℝ) - r.val) * (h + 1) - ((K : ℝ) - r.val) * ((K : ℝ) - r.val + 1) / 2) := by
    intro r
    simp only [bvec]
    rw [icc_sum]
    have : ((K - r.val : ℕ) : ℝ) = (K : ℝ) - r.val := by
      rw [Nat.cast_sub r.isLt.le]
    rw [this]
  set w : Fin K → ℝ := fun r => avec ℓ T r + 1 with hwdef
  have hEqW : ∀ r : Fin K, d * tt r * w r - ∑ c, E r c * w c
      = tt r * (tt r - ((K : ℝ) - r.val)) := by
    intro r
    have h1 := hmulVec w r
    have h2 : (M *ᵥ w) r = bvec ℓ T r + ∑ c, M r c := by
      have : w = avec ℓ T + fun _ => 1 := rfl
      rw [this, mulVec_add, Pi.add_apply, hMa]
      simp [mulVec, dotProduct]
    have h3 := hmulVec (fun _ => 1) r
    simp only [mulVec, dotProduct, mul_one] at h3
    rw [h2, h3, hb r, hrho r] at h1
    field_simp at h1
    simp only [htt] at h1 ⊢
    linear_combination (-1 / 2 : ℝ) * h1
  have hMw : ∀ r, (M *ᵥ w) r = tt r * (tt r - ((K : ℝ) - r.val)) / d := by
    intro r
    rw [hmulVec, ← hEqW r]
    field_simp
  -- refined upper bound
  have hrho2 : ∀ r : Fin K, ∑ c, E r c * ((c.val : ℝ) + 1)
      = ((K : ℝ) - r.val) * (3 * r.val * (r.val + 1) + ((K : ℝ) - r.val + 1) * (K + 2 + 2 * r.val)) / 6 := by
    intro r
    rw [Fin.sum_univ_eq_sum_range (fun c => ((K : ℝ) - ((max r.val c : ℕ) : ℝ)) * ((c : ℝ) + 1)) K]
    exact rho2_range K r.val r.isLt.le
  set κ : ℝ := ((ℓ : ℝ) + 1) / d / ((K : ℝ) + 1) with hκ
  have hKr1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hx := comparison M hoff hrow (fun c => κ * ((c.val : ℝ) + 1) - w c) (by
    intro r
    have e : (fun c : Fin K => κ * ((c.val : ℝ) + 1) - w c)
        = (fun c : Fin K => κ * ((c.val : ℝ) + 1)) - w := rfl
    rw [e, mulVec_sub, Pi.sub_apply, hMw, hmulVec]
    have e2 : ∑ c, E r c * (κ * ((c.val : ℝ) + 1)) = κ * ∑ c, E r c * ((c.val : ℝ) + 1) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => by ring
    rw [e2, hrho2 r]
    have hr : (r.val : ℝ) + 1 ≤ K := by
      have := r.isLt; exact_mod_cast this
    have hr0 : (0 : ℝ) ≤ r.val := Nat.cast_nonneg _
    -- polynomial core: 6 d t c ≥ (ℓ+1)(r² + (K+3) r + (K+1)(K+2))
    have hdT : (ℓ : ℝ) ^ 3 + 5 * (ℓ : ℝ) ^ 2 + 7 * ℓ + 3 < 8 * ℓ * d := by
      have h8 : (0 : ℝ) < 8 * ℓ := by positivity
      have hT' := hT
      rw [div_lt_iff₀ h8] at hT'
      rw [hd]; nlinarith
    set ρ := ((K : ℝ) - r.val) * (3 * r.val * (r.val + 1) + ((K : ℝ) - r.val + 1) * (K + 2 + 2 * r.val)) / 6
      with hρ
    have hexpr : tt r * (κ * ((r.val : ℝ) + 1)) - κ * ρ / d - tt r * (tt r - ((K : ℝ) - r.val)) / d
        = (d * tt r * (((ℓ : ℝ) + 1) * (r.val + 1) - ((K : ℝ) + 1) * (tt r - K + r.val))
            - ((ℓ : ℝ) + 1) * ρ) / (d ^ 2 * ((K : ℝ) + 1)) := by
      rw [hκ]; field_simp; ring
    rw [hexpr]
    apply div_nonneg _ (by positivity)
    have hrK : (r.val : ℝ) + 1 ≤ K := hr
    rcases Nat.even_or_odd ℓ with ⟨q, hq⟩ | ⟨q, hq⟩
    · have hhq : h = q := by omega
      have hKq : K = q := by omega
      have hq' : (ℓ : ℝ) = 2 * q := by rw [hq]; push_cast; ring
      have hKq' : (K : ℝ) = q := by rw [hKq]
      have hhq' : (h : ℝ) = q := by rw [hhq]
      have htt : tt r = (q : ℝ) + r.val + 1 := by simp only [htt]; rw [hhq']
      rw [hρ, htt, hKq', hq']
      rw [hKq'] at hrK
      rw [hq'] at hdT
      exact poly_even q r.val d hr0 hrK hdT
    · have hhq : h = q := by omega
      have hKq : K = q + 1 := by omega
      have hq' : (ℓ : ℝ) = 2 * q + 1 := by rw [hq]; push_cast; ring
      have hKq' : (K : ℝ) = q + 1 := by rw [hKq]; push_cast; ring
      have hhq' : (h : ℝ) = q := by rw [hhq]
      have htt : tt r = (q : ℝ) + r.val + 1 := by simp only [htt]; rw [hhq']
      rw [hρ, htt, hKq', hq']
      rw [hKq'] at hrK
      rw [hq'] at hdT
      have hqq : (q : ℝ) = 0 ∨ 1 ≤ (q : ℝ) := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · left; exact_mod_cast h0
        · right; exact_mod_cast h0
      exact poly_odd q r.val d (Nat.cast_nonneg _) hqq hr0 hrK hdT)
  intro c hc
  have h1 := hx ⟨c, hc⟩
  simp only [hwdef] at h1
  have e3 : ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) * ((c : ℝ) + 1) / (((ℓ - ℓ / 2 : ℕ) : ℝ) + 1)
      = κ * ((c : ℝ) + 1) := by
    rw [hκ]; ring
  rw [e3]
  linarith

end AellAux

namespace OSAux

lemma pone_mulVec (n : ℕ) (x : Fin n → ℝ) :
    Pone n *ᵥ x = fun s => x s - (n : ℝ)⁻¹ * ∑ s', x s' := by
  funext s
  simp only [Pone, mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_one, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]

lemma f1j_formula (ℓ T : ℕ) (ω : Fin T → ℝ) (j : Fin (ℓ + 1)) :
    f1j ℓ T ω j = ∑ s, ω (win ℓ j s) ^ 2 - ((T - ℓ : ℕ) : ℝ)⁻¹ * (∑ s, ω (win ℓ j s)) ^ 2
      + 2 * ∑ s, bl ℓ T s * ω (win ℓ j s) := by
  unfold f1j
  rw [pone_mulVec]
  simp only [dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sq]
  ring

/-- The (half) gradient weights of `f1j` at `o`. -/
noncomputable def ee (ℓ T : ℕ) (o : Fin T → ℝ) (j : Fin (ℓ + 1)) (s : Fin (T - ℓ)) : ℝ :=
  o (win ℓ j s) - ((T - ℓ : ℕ) : ℝ)⁻¹ * ∑ s', o (win ℓ j s') + bl ℓ T s

lemma f1_diff (ℓ T : ℕ) (ω o : Fin T → ℝ) :
    f1 ℓ T o + 2 * ∑ j : Fin (ℓ + 1), ∑ s, ee ℓ T o j s * (ω (win ℓ j s) - o (win ℓ j s))
      ≤ f1 ℓ T ω := by
  unfold f1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  rw [f1j_formula, f1j_formula]
  set n := T - ℓ
  set x : Fin n → ℝ := fun s => ω (win ℓ j s)
  set y : Fin n → ℝ := fun s => o (win ℓ j s)
  have hcs : (∑ s, (x s - y s)) ^ 2 ≤ (n : ℝ) * ∑ s, (x s - y s) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun s => x s - y s)
    simpa using this
  have hkey : ((n : ℝ))⁻¹ * (∑ s, (x s - y s)) ^ 2 ≤ ∑ s, (x s - y s) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp only [show ((n : ℕ) : ℝ) = 0 from by exact_mod_cast h0, _root_.inv_zero, zero_mul]
      exact Finset.sum_nonneg (fun s _ => sq_nonneg _)
    · have hn : (0 : ℝ) < n := by exact_mod_cast hpos
      rw [inv_mul_le_iff₀ hn]; exact hcs
  have e1 : ∑ s, (x s - y s) ^ 2 = ∑ s, x s ^ 2 - 2 * ∑ s, x s * y s + ∑ s, y s ^ 2 := by
    have : ∀ s, (x s - y s) ^ 2 = x s ^ 2 - 2 * (x s * y s) + y s ^ 2 := fun s => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have e2 : ∑ s, (x s - y s) = ∑ s, x s - ∑ s, y s := Finset.sum_sub_distrib _ _
  have e3 : ∑ s, ee ℓ T o j s * (ω (win ℓ j s) - o (win ℓ j s))
      = ∑ s, x s * y s - ∑ s, y s ^ 2 - (n : ℝ)⁻¹ * (∑ s, y s) * (∑ s, x s - ∑ s, y s)
        + ∑ s, bl ℓ T s * x s - ∑ s, bl ℓ T s * y s := by
    simp only [ee, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub,
      ← Finset.mul_sum, x, y]
    have : ∀ s, o (win ℓ j s) * ω (win ℓ j s) = ω (win ℓ j s) * o (win ℓ j s) := fun s => mul_comm _ _
    simp only [this, sq]
    ring
  rw [e3]
  rw [e1, e2] at hkey
  change ∑ s, y s ^ 2 - (n : ℝ)⁻¹ * (∑ s, y s) ^ 2 + 2 * ∑ s, bl ℓ T s * y s +
      2 * (∑ s, x s * y s - ∑ s, y s ^ 2 - (n : ℝ)⁻¹ * (∑ s, y s) * (∑ s, x s - ∑ s, y s) +
        ∑ s, bl ℓ T s * x s - ∑ s, bl ℓ T s * y s) ≤
    ∑ s, x s ^ 2 - (n : ℝ)⁻¹ * (∑ s, x s) ^ 2 + 2 * ∑ s, bl ℓ T s * x s
  nlinarith [hkey]

/-- The gradient weight attached to a period. -/
noncomputable def GG (ℓ T : ℕ) (o : Fin T → ℝ) (t : Fin T) : ℝ :=
  ∑ j : Fin (ℓ + 1), ∑ s : Fin (T - ℓ), if win ℓ j s = t then ee ℓ T o j s else 0

lemma reindex (ℓ T : ℕ) (o δ : Fin T → ℝ) :
    ∑ j : Fin (ℓ + 1), ∑ s, ee ℓ T o j s * δ (win ℓ j s) = ∑ t, δ t * GG ℓ T o t := by
  have h1 : ∀ j s, ee ℓ T o j s * δ (win ℓ j s)
      = ∑ t, (if win ℓ j s = t then δ t * ee ℓ T o j s else 0) := by
    intro j s; rw [Finset.sum_ite_eq]; simp [mul_comm]
  simp only [h1, GG, Finset.mul_sum, mul_ite, mul_zero]
  calc ∑ j : Fin (ℓ + 1), ∑ s : Fin (T - ℓ), ∑ t : Fin T,
        (if win ℓ j s = t then δ t * ee ℓ T o j s else 0)
      = ∑ j : Fin (ℓ + 1), ∑ t : Fin T, ∑ s : Fin (T - ℓ),
        (if win ℓ j s = t then δ t * ee ℓ T o j s else 0) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma om_antisym (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (t : Fin T) :
    omegaStar ℓ T (Fin.rev t) = -omegaStar ℓ T t := by
  have ht := t.isLt
  have hTl : ℓ ≤ T := by omega
  have hd : ((T : ℝ) - ℓ) ≠ 0 := by
    have : (ℓ : ℝ) + 1 ≤ (T : ℝ) - ℓ := by
      have h2 : ((ℓ + 1 + ℓ : ℕ) : ℝ) ≤ T := by exact_mod_cast (show ℓ + 1 + ℓ ≤ T by omega)
      push_cast at h2; linarith
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    linarith
  unfold omegaStar
  simp only [Fin.val_rev]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 <;>
    first
    | omega
    | norm_num
    | skip
  · field_simp
    ring
  · congr 1
    ext
    simp only
    omega


lemma win_rev (ℓ T : ℕ) (hTl : ℓ ≤ T) (j : Fin (ℓ + 1)) (s : Fin (T - ℓ)) :
    win ℓ (Fin.rev j) (Fin.rev s) = Fin.rev (win ℓ j s) := by
  ext
  simp only [win, Fin.val_rev]
  have := s.isLt; have := j.isLt
  omega

lemma bl_rev (ℓ T : ℕ) (s : Fin (T - ℓ)) : bl ℓ T (Fin.rev s) = -bl ℓ T s := by
  simp only [bl, Fin.val_rev]
  have hs := s.isLt
  have : ((T - ℓ - (s.val + 1) : ℕ) : ℝ) = ((T - ℓ : ℕ) : ℝ) - s.val - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [this]
  ring

noncomputable def SS (ℓ T : ℕ) (o : Fin T → ℝ) (j : Fin (ℓ + 1)) : ℝ := ∑ s, o (win ℓ j s)

lemma SS_rev (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (j : Fin (ℓ + 1)) :
    SS ℓ T (omegaStar ℓ T) (Fin.rev j) = -SS ℓ T (omegaStar ℓ T) j := by
  unfold SS
  rw [← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply, win_rev ℓ T (by omega), om_antisym ℓ T hn, Finset.sum_neg_distrib]

lemma SS_sum (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) :
    ∑ j, SS ℓ T (omegaStar ℓ T) j = 0 := by
  have h := Equiv.sum_comp Fin.revPerm (SS ℓ T (omegaStar ℓ T))
  simp only [Fin.revPerm_apply, SS_rev ℓ T hn, Finset.sum_neg_distrib] at h
  linarith

lemma ee_rev (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (j : Fin (ℓ + 1)) (s : Fin (T - ℓ)) :
    ee ℓ T (omegaStar ℓ T) (Fin.rev j) (Fin.rev s) = -ee ℓ T (omegaStar ℓ T) j s := by
  have h1 := SS_rev ℓ T hn j
  unfold SS at h1
  unfold ee
  rw [h1, bl_rev, win_rev ℓ T (by omega), om_antisym ℓ T hn]
  ring

lemma GG_rev (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (t : Fin T) :
    GG ℓ T (omegaStar ℓ T) (Fin.rev t) = -GG ℓ T (omegaStar ℓ T) t := by
  unfold GG
  rw [← Equiv.sum_comp Fin.revPerm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Equiv.sum_comp Fin.revPerm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Fin.revPerm_apply, win_rev ℓ T (by omega), Fin.rev_inj, ee_rev ℓ T hn]
  split_ifs <;> simp


lemma GG_eq (ℓ T : ℕ) (o : Fin T → ℝ) (t : Fin T) :
    GG ℓ T o t = ∑ j : Fin (ℓ + 1),
      (if h : j.val ≤ t.val ∧ t.val - j.val < T - ℓ then ee ℓ T o j ⟨t.val - j.val, h.2⟩ else 0) := by
  unfold GG
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨t.val - j.val, h.2⟩ : Fin (T - ℓ))]
    · rw [if_pos]; ext; simp only [win]; omega
    · intro b _ hb
      rw [if_neg]
      intro hw; apply hb; ext; simp only [Fin.ext_iff, win] at hw ⊢; omega
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · apply Finset.sum_eq_zero
    intro s _
    rw [if_neg]
    intro hw; apply h; simp only [Fin.ext_iff, win] at hw; have := s.isLt; omega

lemma sum_range_cast (m : ℕ) : ∑ i ∈ Finset.range m, (i : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma GG_mid (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (t : Fin T) (h1 : ℓ ≤ t.val) (h2 : t.val < T - ℓ) :
    GG ℓ T (omegaStar ℓ T) t = 0 := by
  rw [GG_eq]
  have hval : ∀ j : Fin (ℓ + 1), j.val ≤ t.val ∧ t.val - j.val < T - ℓ := by
    intro j; have := j.isLt; omega
  rw [Finset.sum_congr rfl (fun j _ => dif_pos (hval j))]
  have hw : ∀ j : Fin (ℓ + 1), win ℓ j ⟨t.val - j.val, (hval j).2⟩ = t := by
    intro j; ext; simp only [win]; have := (hval j).1; omega
  simp only [ee, hw]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hS := SS_sum ℓ T hn
  unfold SS at hS
  rw [hS, mul_zero, sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hTl : ℓ ≤ T := by omega
  have hncast : ((T - ℓ : ℕ) : ℝ) = (T : ℝ) - ℓ := by rw [Nat.cast_sub hTl]
  have hnpos : (0 : ℝ) < (T : ℝ) - ℓ := by
    have : ((ℓ + 1 + ℓ : ℕ) : ℝ) ≤ T := by exact_mod_cast (show ℓ + 1 + ℓ ≤ T by omega)
    push_cast at this
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    linarith
  -- the omega* value in the middle stage
  have hom : omegaStar ℓ T t = -1 + (2 * ((t.val : ℝ) + 1) - ((ℓ : ℝ) + 1)) / ((T : ℝ) - ℓ) := by
    unfold omegaStar
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  have hbl : ∑ j : Fin (ℓ + 1), bl ℓ T ⟨t.val - j.val, (hval j).2⟩
      = ∑ j : Fin (ℓ + 1), (((T : ℝ) - ℓ) - 1 - 2 * t.val + 2 * j.val) / ((T : ℝ) - ℓ) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [bl]
    rw [hncast, Nat.cast_sub (hval j).1]
    ring
  have hj : ∑ j : Fin (ℓ + 1), ((j.val : ℕ) : ℝ) = ((ℓ : ℝ) + 1) * ℓ / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (j : ℝ)) (ℓ + 1), sum_range_cast]; push_cast; ring
  rw [hom, hbl, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
    hj]
  field_simp
  push_cast
  ring


noncomputable def Wf (ℓ T : ℕ) (m : ℕ) : ℝ := if h : m < T then omegaStar ℓ T ⟨m, h⟩ else 0

noncomputable def Qf (ℓ T : ℕ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, Wf ℓ T i

noncomputable def Sf (ℓ T : ℕ) (j : ℕ) : ℝ := ∑ s ∈ Finset.range (T - ℓ), Wf ℓ T (j + s)

noncomputable def Af (ℓ T : ℕ) (c : ℕ) : ℝ := if h : c < ℓ - ℓ / 2 then avec ℓ T ⟨c, h⟩ else 0

lemma Wf_antisym (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (i : ℕ) (hi : i < T) :
    Wf ℓ T (T - 1 - i) = -Wf ℓ T i := by
  have h1 := om_antisym ℓ T hn ⟨i, hi⟩
  unfold Wf
  rw [dif_pos (by omega), dif_pos hi]
  rw [← h1]
  congr 1
  ext; simp only [Fin.val_rev]; omega

lemma Wf_total (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) : Qf ℓ T T = 0 := by
  unfold Qf
  have h := Finset.sum_range_reflect (Wf ℓ T) T
  have h2 : ∑ j ∈ Finset.range T, Wf ℓ T (T - 1 - j) = -∑ j ∈ Finset.range T, Wf ℓ T j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact Wf_antisym ℓ T hn i hi
  linarith

lemma Sf_eq (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (j : ℕ) (hj : j ≤ ℓ) :
    Sf ℓ T j = Qf ℓ T (ℓ - j) - Qf ℓ T j := by
  have htot := Wf_total ℓ T hn
  unfold Qf at htot
  have hT : j + ((T - ℓ) + (ℓ - j)) = T := by omega
  have h1 := Finset.sum_range_add (Wf ℓ T) j ((T - ℓ) + (ℓ - j))
  rw [hT] at h1
  have h2 := Finset.sum_range_add (fun x => Wf ℓ T (j + x)) (T - ℓ) (ℓ - j)
  have htail : ∑ i ∈ Finset.range (ℓ - j), Wf ℓ T (j + ((T - ℓ) + i))
      = -∑ i ∈ Finset.range (ℓ - j), Wf ℓ T i := by
    rw [← Finset.sum_range_reflect (Wf ℓ T) (ℓ - j), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have := Wf_antisym ℓ T hn (ℓ - j - 1 - i) (by omega)
    have e : T - 1 - (ℓ - j - 1 - i) = j + ((T - ℓ) + i) := by omega
    rw [e] at this
    exact this
  simp only [← add_assoc] at h2 htail
  unfold Sf Qf
  rw [h1] at htot
  rw [h2] at htot
  linarith

lemma Qf_low (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (m : ℕ) (hm : m ≤ ℓ / 2) : Qf ℓ T m = -m := by
  unfold Qf
  rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℝ))]
  · simp
  · intro i hi
    rw [Finset.mem_range] at hi
    unfold Wf
    rw [dif_pos (by omega)]
    unfold omegaStar
    rw [dif_pos (by simp only; omega)]

lemma Qf_high (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (p : ℕ) (hp : ℓ / 2 + p ≤ ℓ) :
    Qf ℓ T (ℓ / 2 + p) = -((ℓ / 2 : ℕ) : ℝ) + ∑ c ∈ Finset.range p, Af ℓ T c := by
  unfold Qf
  rw [Finset.sum_range_add]
  have := Qf_low ℓ T hn (ℓ / 2) le_rfl
  unfold Qf at this
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.mem_range] at hc
  unfold Wf Af
  rw [dif_pos (by omega), dif_pos (by omega)]
  unfold omegaStar
  rw [dif_neg (by simp only; omega), dif_pos (by simp only; omega)]
  congr 1
  ext; simp only; omega

lemma SS_Sf (ℓ T : ℕ) (j : Fin (ℓ + 1)) :
    SS ℓ T (omegaStar ℓ T) j = Sf ℓ T j.val := by
  unfold SS Sf
  rw [← Fin.sum_univ_eq_sum_range (fun s => Wf ℓ T (j.val + s)) (T - ℓ)]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold Wf
  have : j.val + s.val < T := by have := s.isLt; have := j.isLt; omega
  rw [dif_pos this]
  rfl

lemma exch (A : ℕ → ℝ) (K m : ℕ) (hm : m ≤ K) :
    ∑ j ∈ Finset.range m, ∑ c ∈ Finset.range (K - j), A c
      = ∑ c ∈ Finset.range K, A c * ((min m (K - c) : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have hsplit : ∑ c ∈ Finset.range (K - m), A c
        = ∑ c ∈ Finset.range K, A c * (if c < K - m then (1 : ℝ) else 0) := by
      have e : ∀ c, A c * (if c < K - m then (1 : ℝ) else 0)
          = if c ∈ Finset.range (K - m) then A c else 0 := by
        intro c; simp only [Finset.mem_range]; split_ifs <;> ring
      simp only [e]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.range_subset_range.mpr (by omega))]
    rw [hsplit, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    by_cases h : c < K - m
    · rw [if_pos h, show min (m + 1) (K - c) = min m (K - c) + 1 by omega]; push_cast; ring
    · rw [if_neg h, show min (m + 1) (K - c) = min m (K - c) by omega]; ring


lemma GG_low_formula (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (t : Fin T) (ht : t.val < ℓ) :
    ((T : ℝ) - ℓ) * GG ℓ T (omegaStar ℓ T) t
      = ((t.val : ℝ) + 1) * (((T : ℝ) - ℓ) * omegaStar ℓ T t + ((T : ℝ) - ℓ) - 1 - t.val)
        - ∑ j ∈ Finset.range (t.val + 1), Sf ℓ T j := by
  have hTl : ℓ ≤ T := by omega
  have hncast : ((T - ℓ : ℕ) : ℝ) = (T : ℝ) - ℓ := by rw [Nat.cast_sub hTl]
  have hnpos : (0 : ℝ) < (T : ℝ) - ℓ := by
    have : ((ℓ + 1 + ℓ : ℕ) : ℝ) ≤ T := by exact_mod_cast (show ℓ + 1 + ℓ ≤ T by omega)
    push_cast at this
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    linarith
  set H : ℕ → ℝ := fun j => omegaStar ℓ T t - ((T : ℝ) - ℓ)⁻¹ * Sf ℓ T j
      + (((T : ℝ) - ℓ) - 1 - 2 * ((t.val : ℝ) - j)) / ((T : ℝ) - ℓ) with hH
  have step1 : ∀ j : Fin (ℓ + 1),
      (if h : j.val ≤ t.val ∧ t.val - j.val < T - ℓ then
        ee ℓ T (omegaStar ℓ T) j ⟨t.val - j.val, h.2⟩ else 0)
      = if j.val ≤ t.val then H j.val else 0 := by
    intro j
    by_cases hj : j.val ≤ t.val
    · have hc : j.val ≤ t.val ∧ t.val - j.val < T - ℓ := ⟨hj, by omega⟩
      rw [dif_pos hc, if_pos hj]
      have hw : win ℓ j ⟨t.val - j.val, hc.2⟩ = t := by ext; simp only [win]; omega
      have hS := SS_Sf ℓ T j
      unfold SS at hS
      simp only [ee, hw, hS, hH, bl, hncast]
      rw [Nat.cast_sub hj]
      ring
    · rw [dif_neg (fun h => hj h.1), if_neg hj]
  rw [GG_eq, Finset.sum_congr rfl (fun j _ => step1 j)]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ t.val then H j else 0) (ℓ + 1)]
  have hsplit : ℓ + 1 = (t.val + 1) + (ℓ - t.val) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hz : ∑ x ∈ Finset.range (ℓ - t.val), (if t.val + 1 + x ≤ t.val then H (t.val + 1 + x) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro x _; rw [if_neg (by omega)]
  rw [hz, add_zero]
  rw [Finset.sum_congr rfl (fun j hj => if_pos (by rw [Finset.mem_range] at hj; omega))]
  simp only [hH, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum]
  rw [sum_range_cast]
  push_cast
  field_simp
  ring


lemma Sf_refl (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (j : ℕ) (hj : j ≤ ℓ) :
    Sf ℓ T (ℓ - j) = -Sf ℓ T j := by
  rw [Sf_eq ℓ T hn j hj, Sf_eq ℓ T hn (ℓ - j) (by omega), show ℓ - (ℓ - j) = j by omega]
  ring

lemma Ssum_refl (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (t : ℕ) (ht : t < ℓ) :
    ∑ j ∈ Finset.range (t + 1), Sf ℓ T j = ∑ j ∈ Finset.range (ℓ - t), Sf ℓ T j := by
  have htot : ∑ j ∈ Finset.range (ℓ + 1), Sf ℓ T j = 0 := by
    have h := Finset.sum_range_reflect (Sf ℓ T) (ℓ + 1)
    have h2 : ∑ j ∈ Finset.range (ℓ + 1), Sf ℓ T (ℓ + 1 - 1 - j)
        = -∑ j ∈ Finset.range (ℓ + 1), Sf ℓ T j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show ℓ + 1 - 1 - j = ℓ - j by omega]
      exact Sf_refl ℓ T hn j (by omega)
    linarith
  have hsplit : ℓ + 1 = (t + 1) + (ℓ - t) := by omega
  rw [hsplit, Finset.sum_range_add] at htot
  have htail : ∑ x ∈ Finset.range (ℓ - t), Sf ℓ T (t + 1 + x)
      = -∑ j ∈ Finset.range (ℓ - t), Sf ℓ T j := by
    rw [← Finset.sum_range_reflect (Sf ℓ T) (ℓ - t), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_range] at hx
    have := Sf_refl ℓ T hn (t + 1 + x) (by omega)
    rw [show ℓ - (t + 1 + x) = ℓ - t - 1 - x by omega] at this
    linarith
  rw [htail] at htot
  linarith

lemma sum_range_sub (m : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range m, ((j : ℝ) - x) = (m : ℝ) * ((m : ℝ) - 1) / 2 - m * x := by
  rw [Finset.sum_sub_distrib, sum_range_cast]; simp

lemma Ssum_low (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (m : ℕ) (hm : m ≤ ℓ - ℓ / 2) :
    ∑ j ∈ Finset.range m, Sf ℓ T j
      = ∑ j ∈ Finset.range m, ((j : ℝ) - ((ℓ / 2 : ℕ) : ℝ))
        + ∑ c ∈ Finset.range (ℓ - ℓ / 2), Af ℓ T c * ((min m (ℓ - ℓ / 2 - c) : ℕ) : ℝ) := by
  rw [← exch (Af ℓ T) (ℓ - ℓ / 2) m hm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Sf_eq ℓ T hn j (by omega)]
  have e : ℓ - j = ℓ / 2 + (ℓ - ℓ / 2 - j) := by omega
  rw [e, Qf_high ℓ T hn _ (by omega), Qf_low ℓ T hn j (by omega)]
  ring

lemma icc_sum (m : ℕ) (x : ℝ) :
    ∑ l ∈ Finset.Icc 1 m, (x - (l : ℝ)) = m * x - (m : ℝ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast; ring

lemma alg1 (d X a τ E : ℝ) (hd : d ≠ 0) (h : τ * a - X / d = -τ + τ ^ 2 / d - 1 / d * E) :
    d * (τ * a) - X = -d * τ + τ ^ 2 - E := by
  field_simp at h
  linear_combination h

lemma GG_stage2 (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ) (hMa : Mmat ℓ T *ᵥ avec ℓ T = bvec ℓ T)
    (t : Fin T) (h1 : ℓ / 2 ≤ t.val) (h2 : t.val < ℓ) : GG ℓ T (omegaStar ℓ T) t = 0 := by
  have hTl : ℓ ≤ T := by omega
  have hnpos : (0 : ℝ) < (T : ℝ) - ℓ := by
    have : ((ℓ + 1 + ℓ : ℕ) : ℝ) ≤ T := by exact_mod_cast (show ℓ + 1 + ℓ ≤ T by omega)
    push_cast at this
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    linarith
  have hf := GG_low_formula ℓ T hn t h2
  set K := ℓ - ℓ / 2 with hK
  set h := ℓ / 2 with hh
  set r : Fin K := ⟨t.val - h, by omega⟩ with hr
  have hom : omegaStar ℓ T t = avec ℓ T r := by
    unfold omegaStar
    rw [dif_neg (by omega), dif_pos (by omega)]
  rw [Ssum_refl ℓ T hn t.val h2, Ssum_low ℓ T hn (ℓ - t.val) (by omega), hom] at hf
  -- row r of M a = b
  have hrow := congrFun hMa r
  have hrow0 : (Mmat ℓ T *ᵥ avec ℓ T) r = (((ℓ / 2 : ℕ) : ℝ) + r.val + 1) * avec ℓ T r
      - (∑ c : Fin (ℓ - ℓ / 2), (((ℓ - ℓ / 2 : ℕ) : ℝ) - ((max r.val c.val : ℕ) : ℝ)) * avec ℓ T c)
        / ((T : ℝ) - ℓ) := by
    have e : ∀ c, Mmat ℓ T r c * avec ℓ T c = (if r = c then (((ℓ / 2 : ℕ) : ℝ) + r.val + 1) * avec ℓ T c else 0)
        - ((((ℓ - ℓ / 2 : ℕ) : ℝ) - ((max r.val c.val : ℕ) : ℝ)) * avec ℓ T c) / ((T : ℝ) - ℓ) := by
      intro c; simp only [Mmat, Matrix.of_apply]; split_ifs <;> ring
    rw [mulVec, dotProduct, Finset.sum_congr rfl (fun c _ => e c), Finset.sum_sub_distrib,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ← Finset.sum_div]
  have hb0 : bvec ℓ T r = -(((ℓ / 2 : ℕ) : ℝ) + r.val + 1) + (((ℓ / 2 : ℕ) : ℝ) + r.val + 1) ^ 2 / ((T : ℝ) - ℓ)
      - (1 / ((T : ℝ) - ℓ)) * (((ℓ - ℓ / 2 - r.val : ℕ) : ℝ) * (((ℓ / 2 : ℕ) : ℝ) + 1)
        - ((ℓ - ℓ / 2 - r.val : ℕ) : ℝ) * (((ℓ - ℓ / 2 - r.val : ℕ) : ℝ) + 1) / 2) := by
    simp only [bvec]
    rw [icc_sum]
  rw [hrow0, hb0] at hrow
  have hconv : ∑ c : Fin (ℓ - ℓ / 2), (((ℓ - ℓ / 2 : ℕ) : ℝ) - ((max r.val c.val : ℕ) : ℝ)) * avec ℓ T c
      = ∑ c ∈ Finset.range K, Af ℓ T c * ((min (ℓ - t.val) (K - c) : ℕ) : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun c => Af ℓ T c * ((min (ℓ - t.val) (K - c) : ℕ) : ℝ)) K]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hc := c.isLt
    unfold Af
    rw [dif_pos hc]
    have e : ((ℓ - ℓ / 2 : ℕ) : ℝ) - ((max r.val c.val : ℕ) : ℝ) = ((min (ℓ - t.val) (K - c) : ℕ) : ℝ) := by
      have : min (ℓ - t.val) (K - c.val) + max r.val c.val = K := by simp only [hr]; omega
      have : ((min (ℓ - t.val) (K - c.val) : ℕ) : ℝ) + ((max r.val c.val : ℕ) : ℝ) = K := by
        exact_mod_cast this
      change ((K : ℕ) : ℝ) - _ = _
      linarith
    rw [e]
    ring
  rw [hconv] at hrow
  rw [sum_range_sub] at hf
  have hKr : ((ℓ - ℓ / 2 - r.val : ℕ) : ℝ) = (ℓ : ℝ) - t.val := by
    rw [show ℓ - ℓ / 2 - r.val = ℓ - t.val by simp only [hr]; omega, Nat.cast_sub h2.le]
  have hlt : ((ℓ - t.val : ℕ) : ℝ) = (ℓ : ℝ) - t.val := by rw [Nat.cast_sub h2.le]
  have htr : ((ℓ / 2 : ℕ) : ℝ) + r.val = t.val := by
    simp only [hr]; rw [Nat.cast_sub h1]; ring
  rw [hKr] at hrow
  rw [hlt] at hf
  have hne : ((T : ℝ) - ℓ) ≠ 0 := hnpos.ne'
  have hrow' : ((T : ℝ) - ℓ) * ((t.val + 1) * avec ℓ T r)
      - ∑ c ∈ Finset.range K, Af ℓ T c * ((min (ℓ - t.val) (ℓ - ℓ / 2 - c) : ℕ) : ℝ)
      = -((T : ℝ) - ℓ) * (t.val + 1) + (t.val + 1) ^ 2
        - (((ℓ : ℝ) - t.val) * (((ℓ / 2 : ℕ) : ℝ) + 1) - ((ℓ : ℝ) - t.val) * (((ℓ : ℝ) - t.val) + 1) / 2) := by
    have e1 : ((ℓ / 2 : ℕ) : ℝ) + r.val + 1 = t.val + 1 := by linarith
    rw [e1] at hrow
    exact alg1 _ _ _ _ _ hne hrow
  have hmain : ((T : ℝ) - ℓ) * GG ℓ T (omegaStar ℓ T) t = 0 := by
    rw [hf]
    rw [← htr] at hrow' ⊢
    linear_combination hrow'
  rcases mul_eq_zero.mp hmain with h0 | h0
  · exact absurd h0 hne
  · exact h0


lemma sum_cK (K : ℕ) : ∑ c ∈ Finset.range K, ((c : ℝ) + 1) * ((K : ℝ) - c)
    = (K : ℝ) * (K + 1) * (K + 2) / 6 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have e : ∀ c ∈ Finset.range K, ((c : ℝ) + 1) * (((K + 1 : ℕ) : ℝ) - c)
        = ((c : ℝ) + 1) * ((K : ℝ) - c) + ((c : ℝ) + 1) := by
      intro c _; push_cast; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih, Finset.sum_add_distrib, sum_range_cast]
    simp
    ring

lemma GG_stage1 (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ)
    (hT : ((ℓ : ℝ) ^ 3 + 13 * (ℓ : ℝ) ^ 2 + 7 * (ℓ : ℝ) + 3) / (8 * (ℓ : ℝ)) < (T : ℝ))
    (hw0 : ∀ c (hc : c < ℓ - ℓ / 2), -1 ≤ avec ℓ T ⟨c, hc⟩)
    (hcu : ∀ c (hc : c < ℓ - ℓ / 2), avec ℓ T ⟨c, hc⟩ + 1
      ≤ ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) * ((c : ℝ) + 1) / (((ℓ - ℓ / 2 : ℕ) : ℝ) + 1))
    (t : Fin T) (ht : t.val < ℓ / 2) : 0 ≤ GG ℓ T (omegaStar ℓ T) t := by
  have h2 : t.val < ℓ := by omega
  have hℓ : 0 < ℓ := by omega
  have hTl : ℓ ≤ T := by omega
  have hnpos : (0 : ℝ) < (T : ℝ) - ℓ := by
    have : ((ℓ + 1 + ℓ : ℕ) : ℝ) ≤ T := by exact_mod_cast (show ℓ + 1 + ℓ ≤ T by omega)
    push_cast at this
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    linarith
  have hf := GG_low_formula ℓ T hn t h2
  set K := ℓ - ℓ / 2 with hK
  set h := ℓ / 2 with hh
  set m := t.val + 1 with hm
  have hom : omegaStar ℓ T t = -1 := by
    unfold omegaStar; rw [dif_pos (by omega)]
  rw [hom, Ssum_low ℓ T hn m (by omega), sum_range_sub] at hf
  -- split Af = w - 1
  have hA : ∑ c ∈ Finset.range K, Af ℓ T c * ((min m (K - c) : ℕ) : ℝ)
      = ∑ c ∈ Finset.range K, (Af ℓ T c + 1) * ((min m (K - c) : ℕ) : ℝ)
        - ∑ c ∈ Finset.range K, ((min m (K - c) : ℕ) : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => by ring
  have hmin : ∑ c ∈ Finset.range K, ((min m (K - c) : ℕ) : ℝ) = (m : ℝ) * K - (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    have := exch (fun _ => (1 : ℝ)) K m (by omega)
    simp only [one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    rw [← this]
    have e : ∀ j ∈ Finset.range m, ((K - j : ℕ) : ℝ) = (K : ℝ) - j := by
      intro j hj; rw [Finset.mem_range] at hj; rw [Nat.cast_sub (by omega)]
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, sum_range_cast]
    simp
  -- bound the weighted sum
  set κ : ℝ := ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) / ((K : ℝ) + 1) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hbound : ∑ c ∈ Finset.range K, (Af ℓ T c + 1) * ((min m (K - c) : ℕ) : ℝ)
      ≤ κ * ((K : ℝ) * (K + 1) * (K + 2) / 6) := by
    rw [← sum_cK, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    rw [Finset.mem_range] at hc
    have hw := hw0 c hc
    have hu := hcu c hc
    have hAf : Af ℓ T c = avec ℓ T ⟨c, hc⟩ := by unfold Af; rw [dif_pos hc]
    rw [hAf]
    have hmn : ((min m (K - c) : ℕ) : ℝ) ≤ (K : ℝ) - c := by
      rw [← Nat.cast_sub hc.le]; exact_mod_cast min_le_right _ _
    have hmn0 : (0 : ℝ) ≤ ((min m (K - c) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hu' : avec ℓ T ⟨c, hc⟩ + 1 ≤ κ * ((c : ℝ) + 1) := by
      rw [hκ]; rw [show ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) / ((K : ℝ) + 1) * ((c : ℝ) + 1)
        = ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ) * ((c : ℝ) + 1) / ((K : ℝ) + 1) by ring]
      exact hu
    have hc0 : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
    calc (avec ℓ T ⟨c, hc⟩ + 1) * ((min m (K - c) : ℕ) : ℝ)
        ≤ (avec ℓ T ⟨c, hc⟩ + 1) * ((K : ℝ) - c) := mul_le_mul_of_nonneg_left hmn (by linarith)
      _ ≤ κ * ((c : ℝ) + 1) * ((K : ℝ) - c) := by
          apply mul_le_mul_of_nonneg_right hu'
          have : (c : ℝ) + 1 ≤ K := by exact_mod_cast hc
          linarith
      _ = κ * (((c : ℝ) + 1) * ((K : ℝ) - c)) := by ring
  -- the polynomial inequality
  have hpoly : κ * ((K : ℝ) * (K + 1) * (K + 2) / 6) ≤ (m : ℝ) * ((ℓ : ℝ) + 1 - 2 * m) := by
    have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have hdT : (ℓ : ℝ) ^ 3 + 5 * (ℓ : ℝ) ^ 2 + 7 * ℓ + 3 < 8 * ℓ * ((T : ℝ) - ℓ) := by
      have h8 : (0 : ℝ) < 8 * ℓ := by positivity
      rw [div_lt_iff₀ h8] at hT
      nlinarith
    have e : κ * ((K : ℝ) * (K + 1) * (K + 2) / 6)
        = ((ℓ : ℝ) + 1) * K * (K + 2) / (6 * ((T : ℝ) - ℓ)) := by
      rw [hκ]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have hm1 : (1 : ℝ) ≤ m := by simp [hm]
    have hmh : (m : ℝ) ≤ h := by
      have : m ≤ h := by omega
      exact_mod_cast this
    have h2h : (ℓ : ℝ) ≤ 2 * h + 1 := by
      have : ℓ ≤ 2 * h + 1 := by omega
      exact_mod_cast this
    have hfm : (h : ℝ) * ((ℓ : ℝ) + 1 - 2 * h) ≤ (m : ℝ) * ((ℓ : ℝ) + 1 - 2 * m) := by
      nlinarith
    have hdpos := hnpos
    have hfh : ((ℓ : ℝ) + 1) * K * (K + 2) ≤ (h : ℝ) * ((ℓ : ℝ) + 1 - 2 * h) * (6 * ((T : ℝ) - ℓ)) := by
      rcases Nat.even_or_odd ℓ with ⟨q, hq⟩ | ⟨q, hq⟩
      · have hhq : h = q := by omega
        have hKq : K = q := by omega
        rw [hhq, hKq]
        have hq' : (ℓ : ℝ) = 2 * q := by rw [hq]; push_cast; ring
        rw [hq'] at hdT ⊢
        have hq1 : (1 : ℝ) ≤ q := by
          have : 1 ≤ q := by omega
          exact_mod_cast this
        nlinarith
      · have hhq : h = q := by omega
        have hKq : K = q + 1 := by omega
        rw [hhq, hKq]
        push_cast
        have hq' : (ℓ : ℝ) = 2 * q + 1 := by rw [hq]; push_cast; ring
        rw [hq'] at hdT ⊢
        have hq1 : (1 : ℝ) ≤ q := by
          have : 1 ≤ q := by omega
          exact_mod_cast this
        nlinarith
    have h6 : (0 : ℝ) ≤ 6 * ((T : ℝ) - ℓ) := by positivity
    nlinarith
  have hgoal : 0 ≤ ((T : ℝ) - ℓ) * GG ℓ T (omegaStar ℓ T) t := by
    have hKl : (K : ℝ) + h = ℓ := by
      have : K + h = ℓ := by omega
      exact_mod_cast this
    have hmr : ((t.val : ℕ) : ℝ) = (m : ℝ) - 1 := by simp [hm]
    have hexp : ((T : ℝ) - ℓ) * GG ℓ T (omegaStar ℓ T) t
        = (m : ℝ) * ((ℓ : ℝ) + 1 - 2 * m)
          - ∑ c ∈ Finset.range K, (Af ℓ T c + 1) * ((min m (K - c) : ℕ) : ℝ) := by
      rw [hf]
      change _ - (_ - _ + ∑ c ∈ Finset.range K, Af ℓ T c * ((min m (K - c) : ℕ) : ℝ)) = _
      rw [hA, hmin, hmr, ← hKl]
      ring
    rw [hexp]
    linarith [hbound, hpoly]
  exact (mul_nonneg_iff_of_pos_left hnpos).mp hgoal

lemma main_ineq (ℓ T : ℕ) (hn : ℓ + 1 ≤ T - ℓ)
    (hs1 : ∀ t : Fin T, t.val < ℓ / 2 → 0 ≤ GG ℓ T (omegaStar ℓ T) t)
    (hs2 : ∀ t : Fin T, ℓ / 2 ≤ t.val → t.val < ℓ → GG ℓ T (omegaStar ℓ T) t = 0)
    (ω : Fin T → ℝ) (hω : ∀ t, -1 ≤ ω t ∧ ω t ≤ 1) :
    f1 ℓ T (omegaStar ℓ T) ≤ f1 ℓ T ω := by
  have h1 := f1_diff ℓ T ω (omegaStar ℓ T)
  have h2 := reindex ℓ T (omegaStar ℓ T) (fun t => ω t - omegaStar ℓ T t)
  rw [h2] at h1
  have hnn : 0 ≤ ∑ t, (ω t - omegaStar ℓ T t) * GG ℓ T (omegaStar ℓ T) t := by
    apply Finset.sum_nonneg
    intro t _
    have ht := t.isLt
    by_cases ha : t.val < ℓ / 2
    · have ho : omegaStar ℓ T t = -1 := by unfold omegaStar; rw [dif_pos (by omega)]
      rw [ho]
      exact mul_nonneg (by linarith [(hω t).1]) (hs1 t ha)
    by_cases hb : t.val < ℓ
    · rw [hs2 t (by omega) hb, mul_zero]
    by_cases hc : t.val < T - ℓ
    · rw [GG_mid ℓ T hn t (by omega) hc, mul_zero]
    -- reflected part
    have hrr : Fin.rev (Fin.rev t) = t := Fin.rev_rev t
    have hG : GG ℓ T (omegaStar ℓ T) t = -GG ℓ T (omegaStar ℓ T) (Fin.rev t) := by
      have := GG_rev ℓ T hn (Fin.rev t)
      rw [hrr] at this
      exact this
    have hrv : (Fin.rev t).val = T - 1 - t.val := by simp [Fin.val_rev]; omega
    by_cases hd : (Fin.rev t).val < ℓ / 2
    · have ho : omegaStar ℓ T t = 1 := by
        have h3 := om_antisym ℓ T hn (Fin.rev t)
        rw [hrr] at h3
        have ho' : omegaStar ℓ T (Fin.rev t) = -1 := by
          unfold omegaStar; rw [dif_pos (by omega)]
        rw [h3, ho']; norm_num
      rw [ho, hG]
      have := hs1 (Fin.rev t) hd
      have := (hω t).2
      nlinarith
    · rw [hG, hs2 (Fin.rev t) (by omega) (by omega)]
      simp
  linarith

end OSAux

open OSAux

theorem solution (ℓ T : ℕ)
    (hT : 0 < ℓ → ((ℓ : ℝ) ^ 3 + 13 * (ℓ : ℝ) ^ 2 + 7 * (ℓ : ℝ) + 3) / (8 * (ℓ : ℝ)) < (T : ℝ)) :
    Monotone (omegaStar ℓ T) ∧ (∀ t, -1 ≤ omegaStar ℓ T t ∧ omegaStar ℓ T t ≤ 1) ∧
    ∀ ω : Fin T → ℝ, Monotone ω → (∀ t, -1 ≤ ω t ∧ ω t ≤ 1) →
      f1 ℓ T (omegaStar ℓ T) ≤ f1 ℓ T ω := by
  by_cases hℓ : 0 < ℓ
  · have hT' := hT hℓ
    obtain ⟨hdet, hab, hamono, hmono, hbd⟩ := StaggeredRollout.TOpt.a_ell_feasible ℓ T hℓ hT'
    have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have h2T : 2 * ℓ < T := by
      have h8 : (0 : ℝ) < 8 * ℓ := by positivity
      have hT2 := hT'
      rw [div_lt_iff₀ h8] at hT2
      have : (2 * ℓ : ℝ) < T := by nlinarith [sq_nonneg ((ℓ : ℝ) - 3 / 2)]
      exact_mod_cast this
    have hn : ℓ + 1 ≤ T - ℓ := by omega
    refine ⟨hmono, hbd, ?_⟩
    intro ω _ hω
    have hMa : Mmat ℓ T *ᵥ avec ℓ T = bvec ℓ T := by
      unfold avec
      rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hdet), one_mulVec]
    have hcu := AellAux.cu_bound ℓ T hℓ hT'
    have hw0 : ∀ c (hc : c < ℓ - ℓ / 2), -1 ≤ avec ℓ T ⟨c, hc⟩ := fun c hc => (hab _).1
    exact main_ineq ℓ T hn (fun t ht => GG_stage1 ℓ T hn hT' hw0 hcu t ht)
      (fun t h1 h2 => GG_stage2 ℓ T hn hMa t h1 h2) ω hω
  · have hℓ0 : ℓ = 0 := by omega
    subst hℓ0
    rcases Nat.eq_zero_or_pos T with hT0 | hTpos
    · subst hT0
      refine ⟨fun t => t.elim0, fun t => t.elim0, ?_⟩
      intro ω _ _
      simp [f1, f1j, dotProduct, bl]
    have hn : 0 + 1 ≤ T - 0 := by omega
    have h2T : 2 * 0 < T := by omega
    have hd1 : ((0 : ℕ) : ℝ) + 1 ≤ (T : ℝ) - ((0 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
      simp; linarith
    have hab : ∀ r : Fin (0 - 0 / 2), -1 ≤ avec 0 T r ∧
        avec 0 T r ≤ -1 + (((0 : ℕ) : ℝ) + 1) / ((T : ℝ) - ((0 : ℕ) : ℝ)) :=
      fun r => absurd r.isLt (by simp)
    have hamono : Monotone (avec 0 T) := fun r => absurd r.isLt (by simp)
    obtain ⟨hmono, hbd⟩ := AellAux.omega_part 0 T h2T hd1 hab hamono
    refine ⟨hmono, hbd, ?_⟩
    intro ω _ hω
    exact main_ineq 0 T hn (fun t ht => absurd ht (by simp)) (fun t _ h2 => absurd h2 (by simp)) ω hω
