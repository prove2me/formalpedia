-- Prove2me | solution 1 for YieldCheapTalk.Truthful.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:21:02.006211+00:00
-- url     : https://prove2.me/submissions/ccc4ef05-3813-44df-931f-04a3be95715c

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
namespace Model
variable (M : Model)

lemma sum_level (f : Level → ℝ) : ∑ m, f m = f .H + f .L := by
  have : (Finset.univ : Finset Level) = {Level.H, Level.L} := rfl
  rw [this, Finset.sum_pair (by intro h; cases h)]

lemma mu_sum (hM : M.Standing) (t : Level) : M.mu .H t + M.mu .L t = 1 := by
  have h1 := hM.p_pos t .H
  have h2 := hM.p_pos t .L
  unfold mu
  rw [sum_level]
  field_simp

lemma theta_pos (hM : M.Standing) (t : Level) : 0 < M.theta t := by
  have h0 : 0 ≤ M.theta t := by
    rw [← hM.mean t]
    apply integral_nonneg_of_ae
    filter_upwards [hM.support t] with x hx using hx.1
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    have := hM.buyer_pos .H t
    rw [← h] at this
    have h3 := hM.eta_mem
    have h4 := hM.w_pos
    nlinarith [h3.1, mul_nonneg h3.1 h4.le]

lemma xi_int (hM : M.Standing) (t : Level) (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (M.xi t) := by
  have := hM.isProb t
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (continuous_pow n).aestronglyMeasurable
  · filter_upwards [hM.support t] with x hx
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact pow_le_one₀ hx.1 hx.2

lemma xi_sq (hM : M.Standing) (t : Level) :
    ∫ x, x ^ 2 ∂(M.xi t) = (1 + M.delta ^ 2) * M.theta t ^ 2 := by
  have := hM.isProb t
  have h := hM.var t
  have e : (fun x : ℝ => (x - M.theta t) ^ 2) = fun x => x ^ 2 + (-(2 * M.theta t)) * x + M.theta t ^ 2 := by
    funext x; ring
  rw [e] at h
  have i1 := xi_int M hM t 2
  have i2 := xi_int M hM t 1
  simp only [pow_one] at i2
  have j1 : Integrable (fun x : ℝ => x ^ 2 + (-(2 * M.theta t)) * x) (M.xi t) := i1.add (i2.const_mul _)
  rw [integral_add j1 (integrable_const _), integral_add i1 (i2.const_mul _),
    integral_const_mul] at h
  have hm := hM.mean t
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  rw [hm] at h
  nlinarith

lemma profitYield_eq (hM : M.Standing) (t : Level) (a Q : ℝ) :
    M.profitYield (M.xi t) a Q =
      Q * ((a - (1 - M.eta) * M.w) * M.theta t - M.eta * M.w)
        - M.b * (1 + M.delta ^ 2) * M.theta t ^ 2 * Q ^ 2 := by
  have := hM.isProb t
  unfold profitYield
  have e : (fun x : ℝ => x * Q * (a - M.b * (x * Q)) - M.eta * M.w * Q - (1 - M.eta) * M.w * x * Q)
      = fun x => (Q * (a - (1 - M.eta) * M.w)) * x + (-(M.b * Q ^ 2)) * x ^ 2 + (-(M.eta * M.w * Q)) := by
    funext x; ring
  rw [e]
  have i1 := xi_int M hM t 2
  have i2 := xi_int M hM t 1
  simp only [pow_one] at i2
  have j1 : Integrable (fun x : ℝ => (Q * (a - (1 - M.eta) * M.w)) * x + (-(M.b * Q ^ 2)) * x ^ 2) (M.xi t) :=
    (i2.const_mul _).add (i1.const_mul _)
  rw [integral_add j1 (integrable_const _),
    integral_add (i2.const_mul _) (i1.const_mul _), integral_const_mul, integral_const_mul,
    xi_sq M hM t, hM.mean t]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

lemma Qr_pos (hM : M.Standing) (t m : Level) : 0 < M.Qr (M.theta t) (M.a m) := by
  have := hM.buyer_pos m t
  have ht := theta_pos M hM t
  unfold Qr
  have hb := hM.b_pos
  apply div_pos
  · nlinarith
  · positivity

lemma Qr_max (hM : M.Standing) (t m : Level) (Q : ℝ) :
    M.profitYield (M.xi t) (M.a m) Q ≤ M.profitYield (M.xi t) (M.a m) (M.Qr (M.theta t) (M.a m)) ∧
    (M.profitYield (M.xi t) (M.a m) Q = M.profitYield (M.xi t) (M.a m) (M.Qr (M.theta t) (M.a m)) →
      Q = M.Qr (M.theta t) (M.a m)) := by
  have ht := theta_pos M hM t
  have hb := hM.b_pos
  have hd : 0 < 2 * M.b * (1 + M.delta ^ 2) * M.theta t ^ 2 := by positivity
  have hK : 0 < M.b * (1 + M.delta ^ 2) * M.theta t ^ 2 := by positivity
  set N := (M.a m - (1 - M.eta) * M.w) * M.theta t - M.eta * M.w with hN
  have hQ : M.Qr (M.theta t) (M.a m) = N / (2 * M.b * (1 + M.delta ^ 2) * M.theta t ^ 2) := rfl
  have key : M.profitYield (M.xi t) (M.a m) (M.Qr (M.theta t) (M.a m)) - M.profitYield (M.xi t) (M.a m) Q
      = M.b * (1 + M.delta ^ 2) * M.theta t ^ 2 * (Q - M.Qr (M.theta t) (M.a m)) ^ 2 := by
    rw [profitYield_eq M hM, profitYield_eq M hM, hQ]
    field_simp
    ring
  have hsq := sq_nonneg (Q - M.Qr (M.theta t) (M.a m))
  constructor
  · nlinarith [mul_nonneg hK.le hsq]
  · intro h
    have : M.b * (1 + M.delta ^ 2) * M.theta t ^ 2 * (Q - M.Qr (M.theta t) (M.a m)) ^ 2 = 0 := by
      rw [← key, h]; ring
    have := (mul_eq_zero.mp this).resolve_left hK.ne'
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linarith


lemma lam_pos (hM : M.Standing) (t m : Level) : 0 < M.lam t m := by
  unfold lam
  apply div_pos (hM.p_pos t m)
  rw [sum_level]
  linarith [hM.p_pos .H m, hM.p_pos .L m]

lemma Qr_diff (hM : M.Standing) (a : ℝ) :
    M.Qr (M.theta .H) a - M.Qr (M.theta .L) a =
      (1 / M.theta .H - 1 / M.theta .L) *
        (a - (1 - M.eta) * M.w - M.eta * M.w * (1 / M.theta .H + 1 / M.theta .L)) /
          (2 * M.b * (1 + M.delta ^ 2)) := by
  have h1 := (theta_pos M hM .H).ne'
  have h2 := (theta_pos M hM .L).ne'
  have hb := hM.b_pos.ne'
  have hd : (1 + M.delta ^ 2) ≠ 0 := by positivity
  unfold Qr
  field_simp
  ring

/-- the combination `E t` -/
noncomputable def E (t : Level) : ℝ :=
  (M.Qr (M.theta .H) (M.a .H) - M.Qr (M.theta .L) (M.a .H)) * M.mu .H t +
    (M.Qr (M.theta .H) (M.a .L) - M.Qr (M.theta .L) (M.a .L)) * M.mu .L t

lemma E_eq (hM : M.Standing) (t : Level) :
    M.E t = (1 / M.theta .H - 1 / M.theta .L) / (2 * M.b * (1 + M.delta ^ 2)) *
      (∑ m, M.mu m t * M.a m - (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w) := by
  unfold E
  rw [Qr_diff M hM, Qr_diff M hM, sum_level]
  have h := mu_sum M hM t
  have hl : M.mu .L t = 1 - M.mu .H t := by linarith
  rw [hl]
  ring

lemma D_neg (hM : M.Standing) : (1 / M.theta .H - 1 / M.theta .L) / (2 * M.b * (1 + M.delta ^ 2)) < 0 := by
  have hb := hM.b_pos
  have h1 : 1 / M.theta .H < 1 / M.theta .L :=
    one_div_lt_one_div_of_lt (theta_pos M hM .L) hM.theta_lt
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

lemma E_nonneg_iff (hM : M.Standing) (t : Level) :
    0 ≤ M.E t ↔ ∑ m, M.mu m t * M.a m ≤ (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w := by
  rw [E_eq M hM]
  have hD := D_neg M hM
  constructor
  · intro h
    by_contra hX
    push Not at hX
    have := mul_neg_of_neg_of_pos hD (sub_pos.mpr hX)
    linarith
  · intro h
    exact mul_nonneg_of_nonpos_of_nonpos hD.le (by linarith)

lemma E_nonpos_iff (hM : M.Standing) (t : Level) :
    M.E t ≤ 0 ↔ (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w ≤ ∑ m, M.mu m t * M.a m := by
  rw [E_eq M hM]
  have hD := D_neg M hM
  constructor
  · intro h
    by_contra hX
    push Not at hX
    have := mul_pos_of_neg_of_neg hD (sub_neg.mpr hX)
    linarith
  · intro h
    exact mul_nonpos_of_nonpos_of_nonneg hD.le (by linarith)

lemma IC5_iff_E : M.IC5 ↔ 0 ≤ M.E .H ∧ M.E .L ≤ 0 := by
  unfold IC5 E
  constructor
  · intro h
    have h1 := h .H .L (by intro h; cases h)
    have h2 := h .L .H (by intro h; cases h)
    constructor <;> linarith
  · rintro ⟨h1, h2⟩ t t' hne
    cases t <;> cases t'
    · exact absurd rfl hne
    · linarith
    · linarith
    · exact absurd rfl hne

lemma high_stmt_iff :
    ((M.Qr (M.theta .H) (M.a .H) - M.Qr (M.theta .L) (M.a .H)) * M.mu .H .H ≥
          (M.Qr (M.theta .L) (M.a .L) - M.Qr (M.theta .H) (M.a .L)) * M.mu .L .H) ↔ 0 ≤ M.E .H := by
  unfold E
  constructor <;> intro h <;> linarith

lemma low_stmt_iff :
    ((M.Qr (M.theta .L) (M.a .H) - M.Qr (M.theta .H) (M.a .H)) * M.mu .H .L ≥
          (M.Qr (M.theta .H) (M.a .L) - M.Qr (M.theta .L) (M.a .L)) * M.mu .L .L) ↔ M.E .L ≤ 0 := by
  unfold E
  constructor <;> intro h <;> linarith

lemma beta_eq (hM : M.Standing) (beta : Level → Level → Level → ℝ)
    (h : ∀ t' m, 0 < ∑ s, (if id s = t' then (1 : ℝ) else 0) * M.lam s m →
      ∀ t, beta t t' m = (if id t = t' then (1 : ℝ) else 0) * M.lam t m /
        ∑ s, (if id s = t' then (1 : ℝ) else 0) * M.lam s m) :
    ∀ t t' m, beta t t' m = if t = t' then 1 else 0 := by
  intro t t' m
  have hsum : ∑ s, (if id s = t' then (1 : ℝ) else 0) * M.lam s m = M.lam t' m := by
    rw [sum_level]; cases t' <;> simp
  have hl := lam_pos M hM t' m
  have := h t' m (by rw [hsum]; exact hl) t
  rw [this, hsum]
  by_cases hh : t = t'
  · subst hh; simp [hl.ne']
  · simp [hh]

lemma profitB_ind (beta : Level → Level → Level → ℝ)
    (hbeta : ∀ t t' m, beta t t' m = if t = t' then 1 else 0) (Q : ℝ) (t' m : Level) :
    M.profitB beta Q t' m = M.profitYield (M.xi t') (M.a m) Q := by
  unfold profitB
  rw [sum_level, hbeta, hbeta]
  cases t' <;> simp

lemma gain_eq (hM : M.Standing) (t : Level) (q : ℝ) :
    ∫ x, (M.eta * M.w + (1 - M.eta) * M.w * x - M.c) * q ∂(M.xi t) =
      (M.eta * M.w + (1 - M.eta) * M.w * M.theta t - M.c) * q := by
  have := hM.isProb t
  have i2 := xi_int M hM t 1
  simp only [pow_one] at i2
  rw [integral_mul_const]
  congr 1
  have e : (fun x : ℝ => M.eta * M.w + (1 - M.eta) * M.w * x - M.c)
      = fun x => ((1 - M.eta) * M.w) * x + (M.eta * M.w - M.c) := by funext x; ring
  rw [e, integral_add (i2.const_mul _) (integrable_const _), integral_const_mul, hM.mean t]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

lemma profitS_eq (hM : M.Standing) (t' t : Level) :
    M.profitS (fun t' m => M.Qr (M.theta t') (M.a m)) t' t =
      (M.eta * M.w + (1 - M.eta) * M.w * M.theta t - M.c) *
        ∑ m, M.mu m t * M.Qr (M.theta t') (M.a m) := by
  unfold profitS
  simp only [gain_eq M hM]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma g_pos (hM : M.Standing) (t : Level) : 0 < M.eta * M.w + (1 - M.eta) * M.w * M.theta t - M.c := by
  linarith [hM.supplier_pos t]

lemma Q_eq (hM : M.Standing) (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ)
    (hP : M.IsPBE id Q beta) : ∀ t m, Q t m = M.Qr (M.theta t) (M.a m) := by
  obtain ⟨_, hB, _, _, hon⟩ := hP
  have hbeta := beta_eq M hM beta hon
  intro t m
  obtain ⟨_, hopt⟩ := hB t m
  have h1 := hopt (M.Qr (M.theta t) (M.a m)) (Qr_pos M hM t m).le
  rw [profitB_ind M beta hbeta, profitB_ind M beta hbeta] at h1
  have h2 := (Qr_max M hM t m (Q t m)).1
  exact (Qr_max M hM t m (Q t m)).2 (le_antisymm h2 h1)

lemma pbe_iff (hM : M.Standing) :
    (∃ (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ), M.IsPBE id Q beta) ↔ M.IC5 := by
  constructor
  · rintro ⟨Q, beta, hP⟩
    have hQ := Q_eq M hM Q beta hP
    have hS := hP.1
    have hQf : Q = fun t' m => M.Qr (M.theta t') (M.a m) := by
      funext t' m; exact hQ t' m
    subst hQf
    intro t t' hne
    have h := hS t t'
    rw [profitS_eq M hM, profitS_eq M hM] at h
    have h' := le_of_mul_le_mul_left h (g_pos M hM t)
    simp only [id] at h'
    rw [sum_level, sum_level] at h'
    linarith
  · intro hIC
    refine ⟨fun t' m => M.Qr (M.theta t') (M.a m), fun (t t' _ : Level) => (if t = t' then 1 else 0 : ℝ), ?_⟩
    have hbeta : ∀ t t' m : Level, (fun (t t' _ : Level) => (if t = t' then 1 else 0 : ℝ)) t t' m = if t = t' then 1 else 0 :=
      fun _ _ _ => rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t t'
      rw [profitS_eq M hM, profitS_eq M hM]
      apply mul_le_mul_of_nonneg_left _ (g_pos M hM t).le
      by_cases h : t = t'
      · subst h; exact le_refl _
      · have := hIC t t' h
        simp only [id]
        rw [sum_level, sum_level]
        linarith
    · intro t' m
      refine ⟨(Qr_pos M hM t' m).le, ?_⟩
      intro Q' hQ'
      rw [profitB_ind M _ hbeta, profitB_ind M _ hbeta]
      exact (Qr_max M hM t' m Q').1
    · intro t t' m; dsimp only; split_ifs <;> norm_num
    · intro t' m; dsimp only; rw [sum_level]; cases t' <;> simp
    · intro t' m hpos t
      have hsum : ∑ s, (if id s = t' then (1 : ℝ) else 0) * M.lam s m = M.lam t' m := by
        rw [sum_level]; cases t' <;> simp
      have hl := lam_pos M hM t' m
      rw [hsum]
      dsimp only
      by_cases hh : t = t'
      · subst hh; simp [hl.ne']
      · simp [hh]
end Model
end YieldCheapTalk.Truthful

open YieldCheapTalk.Truthful

theorem solution (M : Model) (hM : M.Standing) :
    (∃ (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ), M.IsPBE id Q beta) ↔
      (∑ m, M.mu m .H * M.a m ≤ (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w ∧
        (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w ≤
          ∑ m, M.mu m .L * M.a m) := by
  rw [Model.pbe_iff M hM, Model.IC5_iff_E, Model.E_nonneg_iff M hM, Model.E_nonpos_iff M hM]
