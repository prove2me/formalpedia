-- Prove2me | solution 1 for TimelyLoss.Feedback.equations_1_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T08:23:50.550983+00:00
-- url     : https://prove2.me/submissions/779c1305-f4ed-4154-80d6-5d283b4f127c

import Mathlib
import Definitions.Def_TimelyLoss_Feedback_Model

open TimelyLoss.Feedback

namespace TLFSol

noncomputable section

variable (P : Params)

lemma lik_eq (σ : Strategy) (θ : State) (X : ℤ) : lik P σ θ X =
    (1/3) * (P.lam * (if order σ θ + -1 = X then 1 else 0) + (1 - P.lam) * (if -1 = X then 1 else 0)) +
    ((1/3) * (P.lam * (if order σ θ + 0 = X then 1 else 0) + (1 - P.lam) * (if 0 = X then 1 else 0)) +
    (1/3) * (P.lam * (if order σ θ + 1 = X then 1 else 0) + (1 - P.lam) * (if 1 = X then 1 else 0))) := by
  unfold lik noise
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]

lemma lTHm2 : lik P T .H (-2) = 0 := by rw [lik_eq]; norm_num [order, T]
lemma lTHm1 : lik P T .H (-1) = (1 - P.lam)/3 := by rw [lik_eq]; norm_num [order, T]; try ring
lemma lTH0 : lik P T .H 0 = 1/3 := by rw [lik_eq]; norm_num [order, T]; try ring
lemma lTH1 : lik P T .H 1 = 1/3 := by rw [lik_eq]; norm_num [order, T]; try ring
lemma lTH2 : lik P T .H 2 = P.lam/3 := by rw [lik_eq]; norm_num [order, T]; try ring
lemma lTLm2 : lik P T .L (-2) = P.lam/3 := by rw [lik_eq]; norm_num [order, T]; try ring
lemma lTLm1 : lik P T .L (-1) = 1/3 := by rw [lik_eq]; norm_num [order, T]; try ring
lemma lTL0 : lik P T .L 0 = 1/3 := by rw [lik_eq]; norm_num [order, T]; try ring
lemma lTL1 : lik P T .L 1 = (1 - P.lam)/3 := by rw [lik_eq]; norm_num [order, T]; try ring
lemma lTL2 : lik P T .L 2 = 0 := by rw [lik_eq]; norm_num [order, T]
lemma lNTm2 (θ : State) : lik P NT θ (-2) = 0 := by cases θ <;> (rw [lik_eq]; norm_num [order, NT])
lemma lNTm1 (θ : State) : lik P NT θ (-1) = 1/3 := by
  cases θ <;> (rw [lik_eq]; norm_num [order, NT]; try ring)
lemma lNT0 (θ : State) : lik P NT θ 0 = 1/3 := by
  cases θ <;> (rw [lik_eq]; norm_num [order, NT]; try ring)
lemma lNT1 (θ : State) : lik P NT θ 1 = 1/3 := by
  cases θ <;> (rw [lik_eq]; norm_num [order, NT]; try ring)
lemma lNT2 (θ : State) : lik P NT θ 2 = 0 := by cases θ <;> (rw [lik_eq]; norm_num [order, NT])

lemma st (hP : P.Standing) : 0 < P.c ∧ P.c < P.x ∧ P.RL + P.x < P.RH - P.x ∧ 0 < P.β ∧ P.β < 1 ∧
    2 * P.c < P.lam * (P.x + P.c) ∧ 0 < P.lam ∧ P.lam < 1 ∧ 0 < P.f ∧ P.f < 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hP
  have hxc : 0 < P.x + P.c := by linarith
  refine ⟨h1, h2, h3, h4, h5, (div_lt_iff₀ hxc).mp h6, lt_of_le_of_lt (by positivity) h6, h7, h8, h9⟩

lemma post_ne (σ : Strategy) (pr : ℝ) (X : ℤ)
    (h : pr * lik P σ .H X + (1 - pr) * lik P σ .L X ≠ 0) :
    post P σ pr X = pr * lik P σ .H X / (pr * lik P σ .H X + (1 - pr) * lik P σ .L X) := by
  unfold post; rw [if_neg h]

lemma muF_T_m1 (hP : P.Standing) : muF P T (-1) = (1 - P.lam) / (2 - P.lam) := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -⟩ := st P hP
  unfold muF
  rw [post_ne, lTHm1, lTLm1]
  · field_simp; ring
  · rw [lTHm1, lTLm1]; intro h; field_simp at h; linarith

lemma muF_T_1 (hP : P.Standing) : muF P T 1 = 1 / (2 - P.lam) := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -⟩ := st P hP
  unfold muF
  rw [post_ne, lTH1, lTL1]
  · field_simp; ring
  · rw [lTH1, lTL1]; intro h; field_simp at h; linarith

lemma muF_T_0 : muF P T 0 = 1 / 2 := by
  unfold muF
  rw [post_ne, lTH0, lTL0]
  · norm_num
  · rw [lTH0, lTL0]; norm_num

lemma muF_NT (X : ℤ) (hX : X = -1 ∨ X = 0 ∨ X = 1) : muF P NT X = 1 / 2 := by
  have hH : lik P NT .H X = 1/3 := by rcases hX with h | h | h <;> subst h <;> simp [lNTm1, lNT0, lNT1]
  have hL : lik P NT .L X = 1/3 := by rcases hX with h | h | h <;> subst h <;> simp [lNTm1, lNT0, lNT1]
  unfold muF
  rw [post_ne, hH, hL]
  · norm_num
  · rw [hH, hL]; norm_num

lemma key_ineq (hP : P.Standing) : P.c / (2 * P.x) < P.lam / (2 * (2 - P.lam)) := by
  obtain ⟨h1, h2, -, -, -, h6, h7, h8, -, -⟩ := st P hP
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma fr_half (hP : P.Standing) : firmRule P (1 / 2) = .keep := by
  obtain ⟨h1, h2, -⟩ := st P hP
  have : 0 < P.c / (2 * P.x) := by apply div_pos h1; linarith
  unfold firmRule muBar muLow
  rw [if_neg (by linarith), if_neg (by linarith)]

lemma fr_down (hP : P.Standing) : firmRule P ((1 - P.lam) / (2 - P.lam)) = .down := by
  obtain ⟨h1, h2, -, -, -, -, h7, h8, -, -⟩ := st P hP
  have : 0 < P.c / (2 * P.x) := by apply div_pos h1; linarith
  have hk := key_ineq P hP
  have he : (1 - P.lam) / (2 - P.lam) = 1/2 - P.lam / (2 * (2 - P.lam)) := by
    have h2l : (2:ℝ) - P.lam ≠ 0 := by linarith
    field_simp; ring
  unfold firmRule muBar muLow
  rw [if_neg (by rw [he]; linarith), if_pos (by rw [he]; linarith)]

lemma fr_up (hP : P.Standing) : firmRule P (1 / (2 - P.lam)) = .up := by
  obtain ⟨h1, h2, -, -, -, -, h7, h8, -, -⟩ := st P hP
  have hk := key_ineq P hP
  have he : 1 / (2 - P.lam) = 1/2 + P.lam / (2 * (2 - P.lam)) := by
    have h2l : (2:ℝ) - P.lam ≠ 0 := by linarith
    field_simp; ring
  unfold firmRule muBar muLow
  rw [if_pos (by rw [he]; linarith)]


def nH (u : ℝ) : ℝ := 1 - P.f * (P.β - u)
def nL (u : ℝ) : ℝ := 1 - P.f * (P.β + u)
def aa : ℝ := P.f / (2 * (1 - P.f * P.β))
def tf (u : ℝ) : ℝ := 1 / 2 + aa P * u
def τHf (u : ℝ) : ℝ := 1 - (1 - P.f) / nH P u
def τLf (u : ℝ) : ℝ := 1 - (1 - P.f) / nL P u
def Df (u : ℝ) : ℝ := P.RH - P.RL + (τHf P u - τLf P u) * (P.x - P.c)
def Es (u : ℝ) : ℝ := P.RH - P.RL - 2 * (1 - τHf P u) * P.x
def Eb (u : ℝ) : ℝ := P.RH - P.RL + 2 * (1 - τLf P u) * P.x
def ms (u : ℝ) : ℝ := tf P u * (1 - P.lam) / (1 - P.lam * tf P u)
def mb (u : ℝ) : ℝ := tf P u / (1 - P.lam + P.lam * tf P u)
def Gs (u : ℝ) : ℝ := 1 / 3 * (tf P u * Df P u) + 1 / 3 * (ms P u * Es P u)
def Gb (u : ℝ) : ℝ := 1 / 3 * ((1 - tf P u) * Df P u) + 1 / 3 * ((1 - mb P u) * Eb P u)
def GNs (u : ℝ) : ℝ := 2 / 3 * (tf P u * Df P u)
def GNb (u : ℝ) : ℝ := 2 / 3 * ((1 - tf P u) * Df P u)

lemma pN_H (u : ℝ) : probNull P u .H = nH P u := by simp [probNull, betaOf, nH]; ring
lemma pN_L (u : ℝ) : probNull P u .L = nL P u := by simp [probNull, betaOf, nL]; ring

lemma tNull_eq (hP : P.Standing) (u : ℝ) : tNull P u = tf P u := by
  obtain ⟨-, -, -, h4, h5, -, -, -, h9, h10⟩ := st P hP
  have : 0 < 1 - P.f * P.β := by nlinarith
  have hne : 1 - P.f * P.β ≠ 0 := this.ne'
  unfold tNull tf aa; rw [pN_H, pN_L]; unfold nH nL
  rw [show (1/2:ℝ) * (1 - P.f * (P.β - u)) + 1/2 * (1 - P.f*(P.β+u)) = 1 - P.f*P.β by ring]
  field_simp; ring

lemma tauH_eq (u : ℝ) (h : nH P u ≠ 0) : tau P u .H = τHf P u := by
  unfold tau τHf; rw [pN_H]; field_simp; simp [betaOf, nH]; ring

lemma tauL_eq (u : ℝ) (h : nL P u ≠ 0) : tau P u .L = τLf P u := by
  unfold tau τLf; rw [pN_L]; field_simp; simp [betaOf, nL]; ring

/-- positivity region -/
def Pos (u : ℝ) : Prop := 0 < nH P u ∧ 0 < nL P u

lemma tf_bounds (hP : P.Standing) (u : ℝ) (hu : Pos P u) : 0 < tf P u ∧ tf P u < 1 := by
  obtain ⟨-, -, -, h4, h5, -, -, -, h9, h10⟩ := st P hP
  have : 0 < 1 - P.f * P.β := by nlinarith
  obtain ⟨a, b⟩ := hu
  rw [← tNull_eq P hP]
  unfold tNull; rw [pN_H, pN_L]
  constructor
  · apply div_pos <;> linarith
  · rw [div_lt_one (by linarith)]; linarith

lemma Rp_diff (u : ℝ) (hu : Pos P u) : Rprime P u .H - Rprime P u .L = Df P u := by
  unfold Rprime Df; rw [tauH_eq P u hu.1.ne', tauL_eq P u hu.2.ne']; simp [asset]; ring

lemma muM_T_m2 (u : ℝ) : muM P T u (-2) = 0 := by
  unfold muM post; rw [lTHm2]; split_ifs <;> norm_num at *

lemma muM_T_2 (u : ℝ) : muM P T u 2 = 1 := by
  unfold muM post; rw [lTL2]; split_ifs with h h'
  · rfl
  · norm_num at h'
  · rw [mul_zero, add_zero] at h ⊢; exact div_self h

lemma muM_NT_m2 (u : ℝ) : muM P NT u (-2) = 0 := by
  unfold muM post; rw [lNTm2, lNTm2]; simp

lemma muM_NT_2 (u : ℝ) : muM P NT u 2 = 1 := by
  unfold muM post; rw [lNT2, lNT2]; simp

lemma muM_NT (u : ℝ) (X : ℤ) (hX : X = -1 ∨ X = 0 ∨ X = 1) : muM P NT u X = tNull P u := by
  have hH : lik P NT .H X = 1/3 := by rcases hX with h | h | h <;> subst h <;> simp [lNTm1, lNT0, lNT1]
  have hL : lik P NT .L X = 1/3 := by rcases hX with h | h | h <;> subst h <;> simp [lNTm1, lNT0, lNT1]
  unfold muM; rw [post_ne, hH, hL]
  · field_simp; ring
  · rw [hH, hL]; ring_nf; norm_num

lemma muM_T_0 (u : ℝ) : muM P T u 0 = tNull P u := by
  unfold muM; rw [post_ne, lTH0, lTL0]
  · field_simp; ring
  · rw [lTH0, lTL0]; ring_nf; norm_num

lemma muM_T_m1 (hP : P.Standing) (u : ℝ) (hu : Pos P u) : muM P T u (-1) =
    tNull P u * (1 - P.lam) / (tNull P u * (1 - P.lam) + (1 - tNull P u)) := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -⟩ := st P hP
  have ht := tf_bounds P hP u hu
  rw [← tNull_eq P hP] at ht
  have hd : 0 < tNull P u * (1 - P.lam) + (1 - tNull P u) := by nlinarith
  unfold muM; rw [post_ne, lTHm1, lTLm1]
  · field_simp
  · rw [lTHm1, lTLm1]; intro h; nlinarith

lemma muM_T_1 (hP : P.Standing) (u : ℝ) (hu : Pos P u) : muM P T u 1 =
    tNull P u / (tNull P u + (1 - tNull P u) * (1 - P.lam)) := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -⟩ := st P hP
  have ht := tf_bounds P hP u hu
  rw [← tNull_eq P hP] at ht
  have hd : 0 < tNull P u + (1 - tNull P u) * (1 - P.lam) := by nlinarith
  unfold muM; rw [post_ne, lTH1, lTL1]
  · field_simp
  · rw [lTH1, lTL1]; intro h; nlinarith

lemma sell_eq (σ : Strategy) (u : ℝ) : sellProfit P σ u =
    1/3 * (muM P σ u (-2) * (valueGiven P σ u .H (-2) - valueGiven P σ u .L (-2))) +
    (1/3 * (muM P σ u (-1) * (valueGiven P σ u .H (-1) - valueGiven P σ u .L (-1))) +
    1/3 * (muM P σ u 0 * (valueGiven P σ u .H 0 - valueGiven P σ u .L 0))) := by
  unfold sellProfit noise
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  unfold price; norm_num; ring

lemma buy_eq (σ : Strategy) (u : ℝ) : buyProfit P σ u =
    1/3 * ((1 - muM P σ u 0) * (valueGiven P σ u .H 0 - valueGiven P σ u .L 0)) +
    (1/3 * ((1 - muM P σ u 1) * (valueGiven P σ u .H 1 - valueGiven P σ u .L 1)) +
    1/3 * ((1 - muM P σ u 2) * (valueGiven P σ u .H 2 - valueGiven P σ u .L 2))) := by
  unfold buyProfit noise
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  unfold price; norm_num; ring

lemma vg_keep (σ : Strategy) (u : ℝ) (X : ℤ) (h : firmRule P (muF P σ X) = .keep) :
    valueGiven P σ u .H X - valueGiven P σ u .L X = Rprime P u .H - Rprime P u .L := by
  unfold valueGiven Rprime; rw [h]; simp [v, correct, asset]; ring

lemma vg_down (σ : Strategy) (u : ℝ) (X : ℤ) (h : firmRule P (muF P σ X) = .down) :
    valueGiven P σ u .H X - valueGiven P σ u .L X = P.RH - P.RL - 2 * (1 - tau P u .H) * P.x := by
  unfold valueGiven; rw [h]; simp [v, correct, asset]; ring

lemma vg_up (σ : Strategy) (u : ℝ) (X : ℤ) (h : firmRule P (muF P σ X) = .up) :
    valueGiven P σ u .H X - valueGiven P σ u .L X = P.RH - P.RL + 2 * (1 - tau P u .L) * P.x := by
  unfold valueGiven; rw [h]; simp [v, correct, asset]; ring

lemma piNTsell_paper (hP : P.Standing) (u : ℝ) :
    piNTsell P u = (2 / 3 : ℝ) * tNull P u * (Rprime P u .H - Rprime P u .L) := by
  unfold piNTsell; rw [sell_eq, muM_NT_m2, muM_NT P u (-1) (by simp), muM_NT P u 0 (by simp),
    vg_keep P NT u (-1) (by rw [muF_NT P _ (by simp), fr_half P hP]),
    vg_keep P NT u 0 (by rw [muF_NT P _ (by simp), fr_half P hP])]
  ring

lemma piNTbuy_paper (hP : P.Standing) (u : ℝ) :
    piNTbuy P u = (2 / 3 : ℝ) * (1 - tNull P u) * (Rprime P u .H - Rprime P u .L) := by
  unfold piNTbuy; rw [buy_eq, muM_NT_2, muM_NT P u 1 (by simp), muM_NT P u 0 (by simp),
    vg_keep P NT u 1 (by rw [muF_NT P _ (by simp), fr_half P hP]),
    vg_keep P NT u 0 (by rw [muF_NT P _ (by simp), fr_half P hP])]
  ring

lemma piTsell_paper (hP : P.Standing) (u : ℝ) :
    piTsell P u = (1 / 3 : ℝ) * tNull P u * (Rprime P u .H - Rprime P u .L) +
      (1 / 3 : ℝ) * muM P T u (-1) * (P.RH - P.RL - 2 * (1 - tau P u .H) * P.x) := by
  unfold piTsell; rw [sell_eq, muM_T_m2, muM_T_0,
    vg_down P T u (-1) (by rw [muF_T_m1 P hP, fr_down P hP]),
    vg_keep P T u 0 (by rw [muF_T_0, fr_half P hP])]
  ring

lemma piTbuy_paper (hP : P.Standing) (u : ℝ) :
    piTbuy P u = (1 / 3 : ℝ) * (1 - tNull P u) * (Rprime P u .H - Rprime P u .L) +
      (1 / 3 : ℝ) * (1 - muM P T u 1) * (P.RH - P.RL + 2 * (1 - tau P u .L) * P.x) := by
  unfold piTbuy; rw [buy_eq, muM_T_2, muM_T_0,
    vg_up P T u 1 (by rw [muF_T_1 P hP, fr_up P hP]),
    vg_keep P T u 0 (by rw [muF_T_0, fr_half P hP])]
  ring

lemma piNTsell_G (hP : P.Standing) (u : ℝ) (hu : Pos P u) : piNTsell P u = GNs P u := by
  rw [piNTsell_paper P hP, tNull_eq P hP, Rp_diff P u hu]; unfold GNs; ring

lemma piNTbuy_G (hP : P.Standing) (u : ℝ) (hu : Pos P u) : piNTbuy P u = GNb P u := by
  rw [piNTbuy_paper P hP, tNull_eq P hP, Rp_diff P u hu]; unfold GNb; ring

lemma piTsell_G (hP : P.Standing) (u : ℝ) (hu : Pos P u) : piTsell P u = Gs P u := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -⟩ := st P hP
  have ht := tf_bounds P hP u hu
  rw [piTsell_paper P hP, muM_T_m1 P hP u hu, tNull_eq P hP, Rp_diff P u hu,
    tauH_eq P u hu.1.ne']
  unfold Gs ms Es
  rw [show tf P u * (1 - P.lam) + (1 - tf P u) = 1 - P.lam * tf P u by ring]
  ring

lemma piTbuy_G (hP : P.Standing) (u : ℝ) (hu : Pos P u) : piTbuy P u = Gb P u := by
  rw [piTbuy_paper P hP, muM_T_1 P hP u hu, tNull_eq P hP, Rp_diff P u hu,
    tauL_eq P u hu.2.ne']
  unfold Gb mb Eb
  rw [show tf P u + (1 - tf P u) * (1 - P.lam) = 1 - P.lam + P.lam * tf P u by ring]
  ring

lemma feas_n (hP : P.Standing) (u : ℝ) (hu : P.Feasible u) :
    1 - P.f ≤ nH P u ∧ 1 - P.f ≤ nL P u := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, h10⟩ := st P hP
  obtain ⟨a, b, c, d⟩ := hu
  unfold nH nL; constructor <;> nlinarith

lemma feas_pos (hP : P.Standing) (u : ℝ) (hu : P.Feasible u) : Pos P u := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, h10⟩ := st P hP
  obtain ⟨a, b⟩ := feas_n P hP u hu
  exact ⟨by linarith, by linarith⟩

lemma ratio_bounds (hP : P.Standing) (n : ℝ) (hn : 1 - P.f ≤ n) :
    0 < (1 - P.f) / n ∧ (1 - P.f) / n ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, h10⟩ := st P hP
  have : 0 < n := by linarith
  exact ⟨div_pos (by linarith) this, (div_le_one this).mpr hn⟩

lemma Df_pos (hP : P.Standing) (u : ℝ) (hu : P.Feasible u) : 0 < Df P u := by
  obtain ⟨h1, h2, h3, -⟩ := st P hP
  obtain ⟨a, b⟩ := feas_n P hP u hu
  obtain ⟨a1, a2⟩ := ratio_bounds P hP _ a
  obtain ⟨b1, b2⟩ := ratio_bounds P hP _ b
  unfold Df τHf τLf
  have : 0 ≤ (1 - (1 - P.f) / nL P u + (1 - P.f) / nH P u) * (P.x - P.c) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma Es_pos (hP : P.Standing) (u : ℝ) (hu : P.Feasible u) : 0 < Es P u := by
  obtain ⟨h1, h2, h3, -⟩ := st P hP
  obtain ⟨a, b⟩ := feas_n P hP u hu
  obtain ⟨a1, a2⟩ := ratio_bounds P hP _ a
  unfold Es τHf
  have : 0 ≤ (1 - (1 - P.f) / nH P u) * P.x := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma aa_pos (hP : P.Standing) : 0 < aa P := by
  obtain ⟨-, -, -, h4, h5, -, -, -, h9, h10⟩ := st P hP
  have : 0 < 1 - P.f * P.β := by nlinarith
  unfold aa; positivity

lemma d_tf (u : ℝ) : HasDerivAt (tf P) (aa P) u := by
  have h := ((hasDerivAt_id' u).const_mul (aa P)).const_add (1 / 2 : ℝ)
  exact h.congr_deriv (by ring)

lemma d_nH (u : ℝ) : HasDerivAt (nH P) P.f u := by
  have h := (((hasDerivAt_id' u).const_sub P.β).const_mul P.f).const_sub (1 : ℝ)
  exact h.congr_deriv (by ring)

lemma d_nL (u : ℝ) : HasDerivAt (nL P) (-P.f) u := by
  have h := (((hasDerivAt_id' u).const_add P.β).const_mul P.f).const_sub (1 : ℝ)
  exact h.congr_deriv (by ring)

lemma d_τH (u : ℝ) (h : nH P u ≠ 0) :
    HasDerivAt (τHf P) ((1 - P.f) * P.f / nH P u ^ 2) u := by
  have h' := ((hasDerivAt_const u (1 - P.f)).div (d_nH P u) h).const_sub (1 : ℝ)
  exact h'.congr_deriv (by ring)

lemma d_τL (u : ℝ) (h : nL P u ≠ 0) :
    HasDerivAt (τLf P) (-((1 - P.f) * P.f / nL P u ^ 2)) u := by
  have h' := ((hasDerivAt_const u (1 - P.f)).div (d_nL P u) h).const_sub (1 : ℝ)
  exact h'.congr_deriv (by ring)

lemma d_Df (u : ℝ) (hu : Pos P u) : HasDerivAt (Df P)
    (((1 - P.f) * P.f / nH P u ^ 2 + (1 - P.f) * P.f / nL P u ^ 2) * (P.x - P.c)) u := by
  have h := (((d_τH P u hu.1.ne').sub (d_τL P u hu.2.ne')).mul_const (P.x - P.c)).const_add (P.RH - P.RL)
  exact h.congr_deriv (by ring)

lemma d_Es (u : ℝ) (hu : Pos P u) : HasDerivAt (Es P)
    (2 * P.x * ((1 - P.f) * P.f / nH P u ^ 2)) u := by
  have h := ((((d_τH P u hu.1.ne').const_sub 1).const_mul 2).mul_const P.x).const_sub (P.RH - P.RL)
  exact h.congr_deriv (by ring)

lemma d_ms (hP : P.Standing) (u : ℝ) (hu : Pos P u) : HasDerivAt (ms P)
    (aa P * (1 - P.lam) / (1 - P.lam * tf P u) ^ 2) u := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -⟩ := st P hP
  have ht := tf_bounds P hP u hu
  have hne : 1 - P.lam * tf P u ≠ 0 := by nlinarith
  have h := ((d_tf P u).mul_const (1 - P.lam)).div (((d_tf P u).const_mul P.lam).const_sub 1) hne
  exact h.congr_deriv (by field_simp; ring)

lemma piTsell_deriv (hP : P.Standing) (ξ : ℝ) (hξ : P.Feasible ξ) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (piTsell P) d ξ := by
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9, h10⟩ := st P hP
  have hu := feas_pos P hP ξ hξ
  have ht := tf_bounds P hP ξ hu
  have hG := (((d_tf P ξ).mul (d_Df P ξ hu)).const_mul (1 / 3 : ℝ)).add
    (((d_ms P hP ξ hu).mul (d_Es P ξ hu)).const_mul (1 / 3 : ℝ))
  refine ⟨_, ?_, hG.congr_of_eventuallyEq ?_⟩
  · have hD := Df_pos P hP ξ hξ
    have hE := Es_pos P hP ξ hξ
    have ha := aa_pos P hP
    have hnH := hu.1
    have hnL := hu.2
    have hl : 0 < 1 - P.lam * tf P ξ := by nlinarith
    have hms : 0 ≤ ms P ξ := by unfold ms; apply div_nonneg <;> nlinarith
    have hq : 0 < (1 - P.f) * P.f / nH P ξ ^ 2 := by apply div_pos <;> nlinarith
    have hq' : 0 < (1 - P.f) * P.f / nL P ξ ^ 2 := by apply div_pos <;> nlinarith
    have hdm : 0 < aa P * (1 - P.lam) / (1 - P.lam * tf P ξ) ^ 2 := by
      apply div_pos <;> nlinarith
    have e1 : 0 < aa P * Df P ξ := mul_pos ha hD
    have e2 : 0 < tf P ξ * (((1 - P.f) * P.f / nH P ξ ^ 2 + (1 - P.f) * P.f / nL P ξ ^ 2) *
        (P.x - P.c)) := mul_pos ht.1 (mul_pos (by linarith) (by linarith))
    have e3 : 0 < aa P * (1 - P.lam) / (1 - P.lam * tf P ξ) ^ 2 * Es P ξ := mul_pos hdm hE
    have e4 : 0 ≤ ms P ξ * (2 * P.x * ((1 - P.f) * P.f / nH P ξ ^ 2)) :=
      mul_nonneg hms (mul_pos (by linarith) hq).le
    linarith
  · have hc1 : ContinuousAt (nH P) ξ := (d_nH P ξ).continuousAt
    have hc2 : ContinuousAt (nL P) ξ := (d_nL P ξ).continuousAt
    filter_upwards [continuousAt_const.eventually_lt hc1 hu.1,
      continuousAt_const.eventually_lt hc2 hu.2] with y hy1 hy2
    exact piTsell_G P hP y ⟨hy1, hy2⟩

lemma piNTsell_deriv (hP : P.Standing) (ξ : ℝ) (hξ : P.Feasible ξ) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (piNTsell P) d ξ := by
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9, h10⟩ := st P hP
  have hu := feas_pos P hP ξ hξ
  have ht := tf_bounds P hP ξ hu
  have hG := ((d_tf P ξ).mul (d_Df P ξ hu)).const_mul (2 / 3 : ℝ)
  refine ⟨_, ?_, hG.congr_of_eventuallyEq ?_⟩
  · have hD := Df_pos P hP ξ hξ
    have ha := aa_pos P hP
    have hnH := hu.1
    have hnL := hu.2
    have hq : 0 < (1 - P.f) * P.f / nH P ξ ^ 2 := by apply div_pos <;> nlinarith
    have hq' : 0 < (1 - P.f) * P.f / nL P ξ ^ 2 := by apply div_pos <;> nlinarith
    have e1 : 0 < aa P * Df P ξ := mul_pos ha hD
    have e2 : 0 < tf P ξ * (((1 - P.f) * P.f / nH P ξ ^ 2 + (1 - P.f) * P.f / nL P ξ ^ 2) *
        (P.x - P.c)) := mul_pos ht.1 (mul_pos (by linarith) (by linarith))
    linarith
  · have hc1 : ContinuousAt (nH P) ξ := (d_nH P ξ).continuousAt
    have hc2 : ContinuousAt (nL P) ξ := (d_nL P ξ).continuousAt
    filter_upwards [continuousAt_const.eventually_lt hc1 hu.1,
      continuousAt_const.eventually_lt hc2 hu.2] with y hy1 hy2
    exact piNTsell_G P hP y ⟨hy1, hy2⟩

lemma feas0 (hP : P.Standing) : P.Feasible 0 := by
  obtain ⟨-, -, -, h4, h5, -⟩ := st P hP
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma tf0 : tf P 0 = 1 / 2 := by simp [tf]

lemma cor2 (hP : P.Standing) : piTsell P 0 < piTbuy P 0 := by
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9, h10⟩ := st P hP
  have hf := feas0 P hP
  have hu := feas_pos P hP 0 hf
  obtain ⟨a, b⟩ := feas_n P hP 0 hf
  obtain ⟨a1, a2⟩ := ratio_bounds P hP _ a
  obtain ⟨b1, b2⟩ := ratio_bounds P hP _ b
  rw [piTsell_G P hP 0 hu, piTbuy_G P hP 0 hu]
  have hl : (2:ℝ) - P.lam ≠ 0 := by linarith
  have e2 : 1 - mb P 0 = ms P 0 := by
    unfold mb ms; rw [tf0]
    rw [show 1 - P.lam + P.lam * (1/2) = (2 - P.lam)/2 by ring,
      show 1 - P.lam * (1/2) = (2 - P.lam)/2 by ring]
    field_simp; ring
  have hms : 0 < ms P 0 := by
    unfold ms; rw [tf0]; apply div_pos <;> linarith
  have hd : Gb P 0 - Gs P 0 = 1 / 3 * ms P 0 * (Eb P 0 - Es P 0) := by
    unfold Gb Gs; rw [e2, tf0]; ring
  have hE : 0 < Eb P 0 - Es P 0 := by
    unfold Eb Es τLf τHf
    have : 0 < 2 * ((1 - P.f) / nL P 0) * P.x + 2 * ((1 - P.f) / nH P 0) * P.x := by
      have : 0 < P.x := by linarith
      positivity
    linarith
  have := mul_pos (mul_pos (by norm_num : (0:ℝ) < 1/3) hms) hE
  linarith

lemma kappaT_deriv (hP : P.Standing) : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ ∈ Set.Ioo (-ε) ε,
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (kappaT P) d ξ := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8, h9, h10⟩ := st P hP
  have hf := feas0 P hP
  have hu := feas_pos P hP 0 hf
  have cs : ContinuousAt (piTsell P) 0 := by
    obtain ⟨d, -, hd⟩ := piTsell_deriv P hP 0 hf
    exact hd.continuousAt
  have cGb : ContinuousAt (Gb P) 0 := by
    have c_tf := (d_tf P 0).continuousAt
    have c_D := (d_Df P 0 hu).continuousAt
    have c_τL := (d_τL P 0 hu.2.ne').continuousAt
    have hne : 1 - P.lam + P.lam * tf P 0 ≠ 0 := by rw [tf0]; linarith
    have c_mb : ContinuousAt (mb P) 0 := c_tf.div (continuousAt_const.add (continuousAt_const.mul c_tf)) hne
    unfold Gb Eb
    fun_prop
  have cb : ContinuousAt (piTbuy P) 0 := by
    apply cGb.congr
    have hc1 : ContinuousAt (nH P) 0 := (d_nH P 0).continuousAt
    have hc2 : ContinuousAt (nL P) 0 := (d_nL P 0).continuousAt
    filter_upwards [continuousAt_const.eventually_lt hc1 hu.1,
      continuousAt_const.eventually_lt hc2 hu.2] with y hy1 hy2
    exact (piTbuy_G P hP y ⟨hy1, hy2⟩).symm
  have ev : ∀ᶠ y in nhds (0:ℝ), piTsell P y < piTbuy P y ∧ (0 < P.β - y ∧ P.β - y < 1) ∧
      (0 < P.β + y ∧ P.β + y < 1) := by
    have c1 : ContinuousAt (fun y : ℝ => P.β - y) 0 := by fun_prop
    have c2 : ContinuousAt (fun y : ℝ => P.β + y) 0 := by fun_prop
    filter_upwards [cs.eventually_lt cb (cor2 P hP),
      continuousAt_const.eventually_lt c1 (by simp; linarith : (0:ℝ) < P.β - 0),
      c1.eventually_lt continuousAt_const (by simp; linarith : P.β - 0 < 1),
      continuousAt_const.eventually_lt c2 (by simp; linarith : (0:ℝ) < P.β + 0),
      c2.eventually_lt continuousAt_const (by simp; linarith : P.β + 0 < 1)] with y a b c d e
    exact ⟨a, ⟨b, c⟩, ⟨d, e⟩⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ev
  refine ⟨ε, hε, fun ξ hξ => ?_⟩
  have hQ : ∀ y ∈ Set.Ioo (-ε) ε, piTsell P y < piTbuy P y ∧ (0 < P.β - y ∧ P.β - y < 1) ∧
      (0 < P.β + y ∧ P.β + y < 1) := by
    intro y hy
    apply hball
    rw [Real.dist_eq, sub_zero, abs_lt]; exact hy
  obtain ⟨-, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hQ ξ hξ
  obtain ⟨d, hd, hD⟩ := piTsell_deriv P hP ξ ⟨b1.le, b2.le, c1.le, c2.le⟩
  refine ⟨d, hd, hD.congr_of_eventuallyEq ?_⟩
  filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with y hy
  exact min_eq_right (hQ y hy).1.le

lemma kappaNT_ineq (hP : P.Standing) (ξh : ℝ) (hpos : 0 < ξh) (hξ : P.Feasible ξh) :
    kappaNT P 0 < kappaNT P ξh ∧ kappaNT P (-ξh) < kappaNT P ξh := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8, h9, h10⟩ := st P hP
  have hf0 := feas0 P hP
  have hfm : P.Feasible (-ξh) := by
    obtain ⟨a, b, c, d⟩ := hξ; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hu := feas_pos P hP ξh hξ
  have hu0 := feas_pos P hP 0 hf0
  have hum := feas_pos P hP (-ξh) hfm
  have ha := aa_pos P hP
  have hD0 := Df_pos P hP 0 hf0
  have hDm := Df_pos P hP (-ξh) hfm
  -- monotonicity of Df
  obtain ⟨a, b⟩ := feas_n P hP ξh hξ
  have hnH0 : nH P 0 = 1 - P.f * P.β := by simp [nH]
  have hnL0 : nL P 0 = 1 - P.f * P.β := by simp [nL]
  have hnHm : nH P (-ξh) = nL P ξh := by unfold nH nL; ring
  have hnLm : nL P (-ξh) = nH P ξh := by unfold nH nL; ring
  have hlt1 : nL P ξh < 1 - P.f * P.β := by unfold nL; nlinarith
  have hlt2 : 1 - P.f * P.β < nH P ξh := by unfold nH; nlinarith
  have hpf : 0 < 1 - P.f := by linarith
  have A1 : (1 - P.f) / (1 - P.f * P.β) < (1 - P.f) / nL P ξh :=
    div_lt_div_of_pos_left hpf hu.2 hlt1
  have A2 : (1 - P.f) / nH P ξh < (1 - P.f) / (1 - P.f * P.β) :=
    div_lt_div_of_pos_left hpf (by linarith) hlt2
  have hxc : 0 < P.x - P.c := by linarith
  have hDξ0 : Df P 0 < Df P ξh := by
    unfold Df τHf τLf; rw [hnH0, hnL0]; nlinarith
  have hDξm : Df P (-ξh) < Df P ξh := by
    unfold Df τHf τLf; rw [hnHm, hnLm]; nlinarith
  have ht1 : 1 / 2 < tf P ξh := by unfold tf; nlinarith
  have htm : tf P (-ξh) = 1 - tf P ξh := by unfold tf; ring
  have hsell : piNTsell P ξh ≤ kappaNT P ξh := le_max_right _ _
  rw [piNTsell_G P hP ξh hu] at hsell
  unfold GNs at hsell
  constructor
  · refine lt_of_lt_of_le ?_ hsell
    unfold kappaNT
    rw [piNTsell_G P hP 0 hu0, piNTbuy_G P hP 0 hu0]
    unfold GNs GNb; rw [tf0]
    rw [show (1:ℝ) - 1/2 = 1/2 by norm_num, max_self]
    nlinarith
  · refine lt_of_lt_of_le ?_ hsell
    unfold kappaNT
    rw [piNTsell_G P hP _ hum, piNTbuy_G P hP _ hum]
    unfold GNs GNb; rw [htm]
    apply max_lt <;> nlinarith

end
end TLFSol


theorem solution (P : Params) (hP : P.Standing) (ξ : ℝ)
    (hξ : P.Feasible ξ) :
    tNull P ξ = 1 / 2 + (1 / 2) * (P.f / (1 - P.f * P.β)) * ξ ∧
    HasDerivAt (tNull P) ((1 / 2) * (P.f / (1 - P.f * P.β))) ξ ∧
    0 < (1 / 2 : ℝ) * (P.f / (1 - P.f * P.β)) := by
  have ha := TLFSol.aa_pos P hP
  have e : TLFSol.aa P = (1 / 2) * (P.f / (1 - P.f * P.β)) := by
    unfold TLFSol.aa; rw [mul_comm (2:ℝ), ← div_div]; ring
  have hfun : tNull P = TLFSol.tf P := funext (TLFSol.tNull_eq P hP)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]; unfold TLFSol.tf; rw [e]
  · rw [hfun, ← e]; exact TLFSol.d_tf P ξ
  · rw [← e]; exact ha
