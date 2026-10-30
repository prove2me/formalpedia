-- Prove2me | solution 1 for StaggeredRollout.TOpt.a_ell_feasible
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:25:25.99399+00:00
-- url     : https://prove2.me/submissions/279c429e-11c0-4448-aea5-f0bf664af344

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Setting

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

end AellAux

open AellAux

theorem solution (ℓ T : ℕ) (hℓ : 0 < ℓ)
    (hT : ((ℓ : ℝ) ^ 3 + 13 * (ℓ : ℝ) ^ 2 + 7 * (ℓ : ℝ) + 3) / (8 * (ℓ : ℝ)) < (T : ℝ)) :
    (Mmat ℓ T).det ≠ 0 ∧
    (∀ r, -1 ≤ avec ℓ T r ∧ avec ℓ T r ≤ -1 + ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ)) ∧
    Monotone (avec ℓ T) ∧
    Monotone (omegaStar ℓ T) ∧
    (∀ t, -1 ≤ omegaStar ℓ T t ∧ omegaStar ℓ T t ≤ 1) := by
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
  -- lower bound
  have hw0 : ∀ r, 0 ≤ w r := by
    apply comparison M hoff hrow w
    intro r
    rw [hMw]
    apply div_nonneg _ hdpos.le
    have := httge r
    have : (0 : ℝ) ≤ h + 1 := by positivity
    simp only [htt] at *
    nlinarith
  -- upper bound
  have hw1 : ∀ r, w r ≤ ((ℓ : ℝ) + 1) / d := by
    have := comparison M hoff hrow (fun r => ((ℓ : ℝ) + 1) / d - w r) (by
      intro r
      have e : (fun r => ((ℓ : ℝ) + 1) / d - w r)
          = (fun _ => ((ℓ : ℝ) + 1) / d) - w := rfl
      rw [e, mulVec_sub, Pi.sub_apply, hMw, hmulVec, ← Finset.sum_mul, hrho r]
      have hr : (r.val : ℝ) + 1 ≤ K := by
        have := r.isLt; exact_mod_cast this
      have hr0 : (0 : ℝ) ≤ r.val := Nat.cast_nonneg _
      have ht := httge r
      have key : 0 ≤ ((ℓ : ℝ) + 1) * (tt r * d - ((K : ℝ) - r.val) * ((K : ℝ) + r.val + 1) / 2)
          - d * (tt r * (tt r - ((K : ℝ) - r.val))) := by
        have e2 : ((ℓ : ℝ) + 1) * (tt r * d - ((K : ℝ) - r.val) * ((K : ℝ) + r.val + 1) / 2)
          - d * (tt r * (tt r - ((K : ℝ) - r.val)))
            = ((K : ℝ) - r.val) * (2 * d * tt r - ((ℓ : ℝ) + 1) * ((K : ℝ) + r.val + 1) / 2) := by
          simp only [htt]; rw [← hKh']; ring
        rw [e2]
        apply mul_nonneg (by linarith)
        have : ((ℓ : ℝ) + 1) * ((K : ℝ) + r.val + 1) ≤ 4 * d * tt r := by
          have h4 : (K : ℝ) + r.val + 1 ≤ 4 * tt r := by linarith
          have h5 : (0 : ℝ) ≤ (K : ℝ) + r.val + 1 := by positivity
          nlinarith
        linarith
      have e3 : tt r * (((ℓ : ℝ) + 1) / d)
          - ((K : ℝ) - r.val) * ((K : ℝ) + r.val + 1) / 2 * (((ℓ : ℝ) + 1) / d) / d
          - tt r * (tt r - ((K : ℝ) - r.val)) / d
          = (((ℓ : ℝ) + 1) * (tt r * d - ((K : ℝ) - r.val) * ((K : ℝ) + r.val + 1) / 2)
          - d * (tt r * (tt r - ((K : ℝ) - r.val)))) / d ^ 2 := by
        field_simp
      rw [e3]
      exact div_nonneg key (by positivity))
    intro r; have := this r; linarith
  have hwle1 : ∀ r, w r ≤ 1 := by
    intro r
    have := hw1 r
    have : ((ℓ : ℝ) + 1) / d ≤ 1 := by rw [div_le_one hdpos]; exact hd1
    linarith
  have hcard : ∀ i : ℕ, ∑ c : Fin K, (if c.val ≤ i then (1 : ℝ) else 0) ≤ i + 1 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun c => if c ≤ i then (1 : ℝ) else 0) K, Finset.sum_boole]
    have : ((Finset.range K).filter (fun c => c ≤ i)).card ≤ i + 1 := by
      calc ((Finset.range K).filter (fun c => c ≤ i)).card ≤ (Finset.range (i + 1)).card := by
            apply Finset.card_le_card
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_range] at hc ⊢
            omega
        _ = i + 1 := Finset.card_range _
    exact_mod_cast this
  have hwmono : Monotone w := by
    apply fin_mono
    intro i hi
    set r : Fin K := ⟨i, by omega⟩
    set r' : Fin K := ⟨i + 1, hi⟩
    have hE' : ∀ c, E r' c = E r c - (if c.val ≤ i then 1 else 0) := by
      intro c
      simp only [hEdef, r, r']
      by_cases hc : c.val ≤ i
      · rw [if_pos hc, max_eq_left (by omega), max_eq_left hc]; push_cast; ring
      · rw [if_neg hc, max_eq_right (by omega), max_eq_right (by omega)]; ring
    have hS : ∑ c, E r' c * w c = ∑ c, E r c * w c - ∑ c, (if c.val ≤ i then w c else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hE']; split_ifs <;> ring
    have hSle : ∑ c : Fin K, (if c.val ≤ i then w c else 0) ≤ i + 1 := by
      refine le_trans (Finset.sum_le_sum fun c _ => ?_) (hcard i)
      split_ifs
      · exact hwle1 c
      · exact le_rfl
    have e1 := hEqW r
    have e2 := hEqW r'
    rw [hS] at e2
    have htr : tt r' = tt r + 1 := by simp only [htt, r, r']; push_cast; ring
    have htr0 : tt r = (h : ℝ) + i + 1 := rfl
    rw [htr] at e2
    have hdw : d * w r ≤ (ℓ : ℝ) + 1 := by
      have := hw1 r
      rw [le_div_iff₀ hdpos] at this; linarith
    have key : 0 ≤ d * (tt r + 1) * (w r' - w r) := by
      have hrv : ((r'.val : ℕ) : ℝ) = (i : ℝ) + 1 := by simp [r']
      have hrv0 : ((r.val : ℕ) : ℝ) = (i : ℝ) := by simp [r]
      rw [hrv] at e2; rw [hrv0] at e1
      nlinarith
    have hpos : 0 < d * (tt r + 1) := by
      have : (0 : ℝ) ≤ tt r := by rw [htr0]; positivity
      positivity
    have := (mul_nonneg_iff_of_pos_left hpos).mp key
    linarith
  have hab : ∀ r, -1 ≤ avec ℓ T r ∧ avec ℓ T r ≤ -1 + ((ℓ : ℝ) + 1) / d := by
    intro r
    have h0 := hw0 r
    have h1 := hw1 r
    simp only [hwdef] at h0 h1
    constructor <;> linarith
  have hamono : Monotone (avec ℓ T) := by
    intro i j hij
    have := hwmono hij
    simp only [hwdef] at this
    linarith
  have hA2 : ∀ i j : Fin (ℓ - ℓ / 2), i.val ≤ j.val → avec ℓ T i ≤ avec ℓ T j :=
    fun i j hij => hamono hij
  exact ⟨hdet, hab, hamono, omega_part ℓ T h2T hd1 hab hamono⟩
