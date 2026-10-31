-- Prove2me | solution 1 for SwitchCostGames.Stationary.value_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:40:18.180223+00:00
-- url     : https://prove2.me/submissions/f5917e2b-67a4-45dc-92af-e5181f86cbfe

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model
import Theorems.Thm_AGT_zero_sum_minimax

open SwitchCostGames.Stationary

namespace SCGAux

theorem take_snoc {m n T : ℕ} (h : History m n T) (x : Fin m × Fin n) (s : ℕ) (hs : s ≤ T) :
    History.take (Fin.snoc h x : History m n (T + 1)) s (hs.trans T.le_succ) =
      History.take h s hs := by
  funext r
  have hr : (r : ℕ) < T := lt_of_lt_of_le r.isLt hs
  simp [History.take, Fin.snoc, hr, Fin.castLT]
  rfl

theorem take_self {m n T : ℕ} (h : History m n T) : History.take h T le_rfl = h := by
  funext r
  simp [History.take]

theorem histProb_snoc {m n T : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) (h : History m n T)
    (x : Fin m × Fin n) :
    histProb σ τ (Fin.snoc h x : History m n (T + 1)) =
      histProb σ τ h * (σ.act T h x.1 * τ.act T h x.2) := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun s _ => ?_)
    have e1 : (Fin.snoc h x : History m n (T + 1)) (Fin.castSucc s) = h s := Fin.snoc_castSucc ..
    have e2 := take_snoc h x s s.isLt.le
    simp only [Fin.val_castSucc]
    rw [e1, e2]
  · have e1 : (Fin.snoc h x : History m n (T + 1)) (Fin.last T) = x := Fin.snoc_last ..
    have e2 := take_snoc h x T le_rfl
    simp only [Fin.val_last]
    rw [e1, e2, take_self]

theorem histProb_nonneg {m n T : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n)
    (h : History m n T) : 0 ≤ histProb σ τ h := by
  unfold histProb
  exact Finset.prod_nonneg (fun s _ =>
    mul_nonneg ((σ.act_mem _ _).1 _) ((τ.act_mem _ _).1 _))

theorem sum_histProb {m n : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) :
    ∀ T : ℕ, ∑ h : History m n T, histProb σ τ h = 1
  | 0 => by simp [histProb]
  | T + 1 => by
    rw [← (Fin.snocEquiv (fun _ : Fin (T + 1) => Fin m × Fin n)).sum_comp]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have key : ∀ h : History m n T,
        ∑ x : Fin m × Fin n, histProb σ τ (Fin.snoc h x : History m n (T + 1)) =
          histProb σ τ h := by
      intro h
      simp only [histProb_snoc]
      rw [← Finset.mul_sum, Fintype.sum_prod_type]
      have : ∑ i : Fin m, ∑ j : Fin n, σ.act T h i * τ.act T h j = 1 := by
        rw [← Finset.sum_mul_sum, (σ.act_mem _ _).2, (τ.act_mem _ _).2, one_mul]
      simp only at this ⊢
      rw [this, mul_one]
    calc ∑ h : History m n T, ∑ x : Fin m × Fin n,
          histProb σ τ (Fin.snoc h x : History m n (T + 1))
        = ∑ h : History m n T, histProb σ τ h := Finset.sum_congr rfl (fun h _ => key h)
      _ = 1 := sum_histProb σ τ T

theorem prevAction_of_const {m n : ℕ} [NeZero n] (j : Fin n) :
    ∀ {t : ℕ} (h : History m n t), (∀ r, (h r).2 = j) → t ≠ 0 → prevAction h = j
  | 0, _, _, ht => absurd rfl ht
  | t + 1, h, hj, _ => hj (Fin.last t)

end SCGAux

namespace SCGAux

open Finset

theorem sum_snoc_histProb {m n T : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n)
    (h : History m n T) :
    ∑ x : Fin m × Fin n, histProb σ τ h * (σ.act T h x.1 * τ.act T h x.2) = histProb σ τ h := by
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  have : ∑ i : Fin m, ∑ j : Fin n, σ.act T h i * τ.act T h j = 1 := by
    rw [← Finset.sum_mul_sum, (σ.act_mem _ _).2, (τ.act_mem _ _).2, one_mul]
  simp only at this ⊢
  rw [this, mul_one]

/-- Marginalization: summing a function of the first `s` stages against the law of histories of
length `T ≥ s` is the same as summing it against the law of histories of length `s`. -/
theorem snocEquiv_eq {m n t : ℕ} (x : Fin m × Fin n) (h : History m n t) :
    (Fin.snocEquiv (fun _ : Fin (t + 1) => Fin m × Fin n)) (x, h) =
      (Fin.snoc h x : History m n (t + 1)) := rfl

theorem marginal {m n : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) :
    ∀ (T s : ℕ) (hs : s ≤ T) (F : History m n s → ℝ),
      ∑ h : History m n T, histProb σ τ h * F (h.take s hs) =
        ∑ h' : History m n s, histProb σ τ h' * F h'
  | 0, s, hs, F => by
    obtain rfl : s = 0 := by omega
    simp only [take_self]
  | T + 1, s, hs, F => by
    rcases eq_or_lt_of_le hs with rfl | hlt
    · simp only [take_self]
    · have hsT : s ≤ T := Nat.lt_succ_iff.1 hlt
      rw [← (Fin.snocEquiv (fun _ : Fin (T + 1) => Fin m × Fin n)).sum_comp,
        Fintype.sum_prod_type, Finset.sum_comm, ← marginal σ τ T s hsT F]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      have e : ∀ x : Fin m × Fin n,
          History.take (Fin.snoc h x : History m n (T + 1)) s hs = History.take h s hsT :=
        fun x => take_snoc h x s hsT
      simp only [snocEquiv_eq, e, histProb_snoc]
      rw [← Finset.sum_mul, sum_snoc_histProb]

end SCGAux


open SCGAux Finset Filter Topology


/-- The stage-`t` reward, read off a history of length `t + 1`. -/
noncomputable def SCGstageR {m n : ℕ} [NeZero n] (G : Game m n) (c : ℝ) (t : ℕ)
    (h : History m n (t + 1)) : ℝ :=
  G.A (h (Fin.last t)).1 (h (Fin.last t)).2 +
    c * G.S (prevAction (h.take t (Nat.le_succ t))) (h (Fin.last t)).2

theorem SCG_expectedTotal_eq {m n : ℕ} [NeZero n] (G : Game m n) (c : ℝ) (σ : Strategy1 m n)
    (τ : Strategy2 m n) (T : ℕ) :
    expectedTotal G c σ τ T = ∑ t ∈ range T,
      ∑ h : History m n (t + 1), histProb σ τ h * SCGstageR G c t h := by
  unfold expectedTotal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Fin.sum_univ_eq_sum_range (fun t => ∑ h : History m n (t + 1),
    histProb σ τ h * SCGstageR G c t h) T]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← marginal σ τ T (s + 1) s.isLt (SCGstageR G c s)]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  congr 1


/-- The stage-`t` expectation, conditioning on the history of the first `t` stages. -/
theorem SCG_stage_gen {m n : ℕ} [NeZero n] (G : Game m n) (c : ℝ) (σ : Strategy1 m n)
    (τ : Strategy2 m n) (t : ℕ) :
    ∑ h : History m n (t + 1), histProb σ τ h * SCGstageR G c t h =
      ∑ h : History m n t, histProb σ τ h * ∑ i, ∑ j, σ.act t h i * τ.act t h j *
        (G.A i j + c * G.S (prevAction h) j) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (t + 1) => Fin m × Fin n)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  have e1 : ∀ x : Fin m × Fin n, (Fin.snoc h x : History m n (t + 1)) (Fin.last t) = x :=
    fun x => Fin.snoc_last ..
  have e2 : ∀ x : Fin m × Fin n,
      History.take (Fin.snoc h x : History m n (t + 1)) t (Nat.le_succ t) = h := by
    intro x
    rw [take_snoc h x t le_rfl, take_self]
  simp only [snocEquiv_eq, histProb_snoc, SCGstageR, e1, e2]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- One step of the law of the state (previous column). -/
theorem SCG_pot_step {m n : ℕ} [NeZero n] (σ : Strategy1 m n) (τ : Strategy2 m n) (t : ℕ)
    (φ : Fin n → ℝ) :
    ∑ h : History m n (t + 1), histProb σ τ h * φ (prevAction h) =
      ∑ h : History m n t, histProb σ τ h * ∑ i, ∑ j, σ.act t h i * τ.act t h j * φ j := by
  rw [← (Fin.snocEquiv (fun _ : Fin (t + 1) => Fin m × Fin n)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  have e1 : ∀ x : Fin m × Fin n, prevAction (Fin.snoc h x : History m n (t + 1)) = x.2 := by
    intro x
    show ((Fin.snoc h x : History m n (t + 1)) (Fin.last t)).2 = x.2
    rw [Fin.snoc_last]
  simp only [snocEquiv_eq, histProb_snoc, e1]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem SCG_mixed_sum {m n T : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) (a : ℝ) :
    ∑ h : History m n T, histProb σ τ h * a = a := by
  rw [← Finset.sum_mul, sum_histProb, one_mul]

theorem SCG_split {m n t : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) (h : History m n t)
    (X Y : Fin m → Fin n → ℝ) :
    ∑ i, ∑ j, σ.act t h i * τ.act t h j * (X i j + Y i j) =
      ∑ i, ∑ j, σ.act t h i * τ.act t h j * X i j +
        ∑ i, ∑ j, σ.act t h i * τ.act t h j * Y i j := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Telescoping lower bound from a potential `φ` (an average-cost optimality inequality). -/
theorem SCG_tele_lower {m n : ℕ} [NeZero n] (G : Game m n) (c : ℝ) (σ : Strategy1 m n)
    (τ : Strategy2 m n) (w : ℝ) (φ : Fin n → ℝ)
    (hcond : ∀ t (h : History m n t), w + φ (prevAction h) ≤
      ∑ i, ∑ j, σ.act t h i * τ.act t h j * (G.A i j + c * G.S (prevAction h) j + φ j)) :
    ∀ T : ℕ, (T : ℝ) * w + φ 0 - ∑ h : History m n T, histProb σ τ h * φ (prevAction h) ≤
      expectedTotal G c σ τ T
  | 0 => by
    simp [expectedTotal, histProb, prevAction]
  | T + 1 => by
    have ih := SCG_tele_lower G c σ τ w φ hcond T
    rw [SCG_expectedTotal_eq, Finset.sum_range_succ, ← SCG_expectedTotal_eq,
      SCG_stage_gen, SCG_pot_step]
    have hw := SCG_mixed_sum (T := T) σ τ w
    have key : w + ∑ h : History m n T, histProb σ τ h * φ (prevAction h) ≤
        ∑ h : History m n T, histProb σ τ h * (∑ i, ∑ j, σ.act T h i * τ.act T h j *
          (G.A i j + c * G.S (prevAction h) j)) +
        ∑ h : History m n T, histProb σ τ h * (∑ i, ∑ j, σ.act T h i * τ.act T h j * φ j) := by
      calc w + ∑ h : History m n T, histProb σ τ h * φ (prevAction h)
          = ∑ h : History m n T, histProb σ τ h * (w + φ (prevAction h)) := by
            conv_lhs => rw [← hw]
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun h _ => by ring)
        _ ≤ ∑ h : History m n T, histProb σ τ h * (∑ i, ∑ j, σ.act T h i * τ.act T h j *
              (G.A i j + c * G.S (prevAction h) j) +
                ∑ i, ∑ j, σ.act T h i * τ.act T h j * φ j) := by
            refine Finset.sum_le_sum (fun h _ =>
              mul_le_mul_of_nonneg_left ?_ (histProb_nonneg σ τ h))
            refine (hcond T h).trans (le_of_eq ?_)
            exact SCG_split σ τ h _ _
        _ = _ := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun h _ => by ring)
    push_cast
    linarith

/-- Telescoping upper bound from a potential `φ`. -/
theorem SCG_tele_upper {m n : ℕ} [NeZero n] (G : Game m n) (c : ℝ) (σ : Strategy1 m n)
    (τ : Strategy2 m n) (w : ℝ) (φ : Fin n → ℝ)
    (hcond : ∀ t (h : History m n t),
      ∑ i, ∑ j, σ.act t h i * τ.act t h j * (G.A i j + c * G.S (prevAction h) j + φ j) ≤
        w + φ (prevAction h)) :
    ∀ T : ℕ, expectedTotal G c σ τ T ≤
      (T : ℝ) * w + φ 0 - ∑ h : History m n T, histProb σ τ h * φ (prevAction h)
  | 0 => by
    simp [expectedTotal, histProb, prevAction]
  | T + 1 => by
    have ih := SCG_tele_upper G c σ τ w φ hcond T
    rw [SCG_expectedTotal_eq, Finset.sum_range_succ, ← SCG_expectedTotal_eq,
      SCG_stage_gen, SCG_pot_step]
    have hw := SCG_mixed_sum (T := T) σ τ w
    have key : ∑ h : History m n T, histProb σ τ h * (∑ i, ∑ j, σ.act T h i * τ.act T h j *
          (G.A i j + c * G.S (prevAction h) j)) +
        ∑ h : History m n T, histProb σ τ h * (∑ i, ∑ j, σ.act T h i * τ.act T h j * φ j) ≤
        w + ∑ h : History m n T, histProb σ τ h * φ (prevAction h) := by
      calc _ = ∑ h : History m n T, histProb σ τ h * (∑ i, ∑ j, σ.act T h i * τ.act T h j *
              (G.A i j + c * G.S (prevAction h) j) +
                ∑ i, ∑ j, σ.act T h i * τ.act T h j * φ j) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun h _ => by ring)
        _ ≤ ∑ h : History m n T, histProb σ τ h * (w + φ (prevAction h)) := by
            refine Finset.sum_le_sum (fun h _ =>
              mul_le_mul_of_nonneg_left ?_ (histProb_nonneg σ τ h))
            refine le_trans (le_of_eq ?_) (hcond T h)
            exact (SCG_split σ τ h _ _).symm
        _ = _ := by
            simp only [mul_add, Finset.sum_add_distrib]
            rw [hw]
    push_cast
    linarith

theorem SCG_pot_bound {m n T : ℕ} [NeZero n] (σ : Strategy1 m n) (τ : Strategy2 m n)
    (φ : Fin n → ℝ) :
    |∑ h : History m n T, histProb σ τ h * φ (prevAction h)| ≤ ∑ k, |φ k| := by
  have hk : ∀ k, |φ k| ≤ ∑ k, |φ k| := fun k =>
    Finset.single_le_sum (f := fun k => |φ k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k)
  rw [abs_le]
  constructor
  · calc -∑ k, |φ k| = ∑ h : History m n T, histProb σ τ h * (-∑ k, |φ k|) :=
          (SCG_mixed_sum σ τ _).symm
      _ ≤ _ := Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left
          (by linarith [neg_abs_le (φ (prevAction h)), hk (prevAction h)])
          (histProb_nonneg σ τ h))
  · calc _ ≤ ∑ h : History m n T, histProb σ τ h * (∑ k, |φ k|) :=
          Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left
            (by linarith [le_abs_self (φ (prevAction h)), hk (prevAction h)])
            (histProb_nonneg σ τ h))
      _ = _ := SCG_mixed_sum σ τ _

theorem SCG_ET_lower {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) (c : ℝ) (hc : 0 ≤ c)
    (σ : Strategy1 m n) (τ : Strategy2 m n) (T : ℕ) :
    (T : ℝ) * Finset.univ.inf' Finset.univ_nonempty (fun p : Fin m × Fin n => G.A p.1 p.2) ≤
      expectedTotal G c σ τ T := by
  unfold expectedTotal
  rw [← SCG_mixed_sum σ τ ((T : ℝ) * _)]
  refine Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left ?_ (histProb_nonneg σ τ h))
  calc (T : ℝ) * _ = ∑ _s : Fin T, Finset.univ.inf' Finset.univ_nonempty
        (fun p : Fin m × Fin n => G.A p.1 p.2) := by simp
    _ ≤ _ := by
      refine Finset.sum_le_sum (fun s _ => ?_)
      have h1 : Finset.univ.inf' Finset.univ_nonempty (fun p : Fin m × Fin n => G.A p.1 p.2) ≤
          G.A (h s).1 (h s).2 :=
        Finset.inf'_le (fun p : Fin m × Fin n => G.A p.1 p.2) (Finset.mem_univ (h s))
      have h2 : 0 ≤ c * G.S (prevAction (h.take s s.isLt.le)) (h s).2 :=
        mul_nonneg hc (G.S_nonneg _ _)
      linarith

theorem SCG_ET_upper {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) (c : ℝ) (hc : 0 ≤ c)
    (σ : Strategy1 m n) (τ : Strategy2 m n) (T : ℕ) :
    expectedTotal G c σ τ T ≤
      (T : ℝ) * (Finset.univ.sup' Finset.univ_nonempty (fun p : Fin m × Fin n => G.A p.1 p.2) +
        c * Finset.univ.sup' Finset.univ_nonempty (fun p : Fin n × Fin n => G.S p.1 p.2)) := by
  unfold expectedTotal
  rw [← SCG_mixed_sum σ τ ((T : ℝ) * _)]
  refine Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left ?_ (histProb_nonneg σ τ h))
  calc
    _ ≤ ∑ _s : Fin T, (Finset.univ.sup' Finset.univ_nonempty
          (fun p : Fin m × Fin n => G.A p.1 p.2) +
          c * Finset.univ.sup' Finset.univ_nonempty (fun p : Fin n × Fin n => G.S p.1 p.2)) := by
        refine Finset.sum_le_sum (fun s _ => ?_)
        have h1 : G.A (h s).1 (h s).2 ≤
            Finset.univ.sup' Finset.univ_nonempty (fun p : Fin m × Fin n => G.A p.1 p.2) :=
          Finset.le_sup' (fun p : Fin m × Fin n => G.A p.1 p.2) (Finset.mem_univ (h s))
        have h2 : G.S (prevAction (h.take s s.isLt.le)) (h s).2 ≤
            Finset.univ.sup' Finset.univ_nonempty (fun p : Fin n × Fin n => G.S p.1 p.2) :=
          Finset.le_sup' (fun p : Fin n × Fin n => G.S p.1 p.2)
            (Finset.mem_univ (prevAction (h.take s s.isLt.le), (h s).2))
        have := mul_le_mul_of_nonneg_left h2 hc
        linarith
    _ = _ := by simp; ring

theorem SCG_payoff_ge {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) (c : ℝ) (hc : 0 ≤ c)
    (σ : Strategy1 m n) (τ : Strategy2 m n) (w : ℝ) (φ : Fin n → ℝ)
    (hcond : ∀ t (h : History m n t), w + φ (prevAction h) ≤
      ∑ i, ∑ j, σ.act t h i * τ.act t h j * (G.A i j + c * G.S (prevAction h) j + φ j)) :
    w ≤ payoff G c σ τ := by
  set Hb := ∑ k, |φ k|
  have hφ0 : -Hb ≤ φ 0 := by
    have := Finset.single_le_sum (f := fun k => |φ k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ 0)
    linarith [neg_abs_le (φ 0)]
  have hg : Tendsto (fun T : ℕ => w - 2 * Hb / (T : ℝ)) atTop (𝓝 w) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (2 * Hb)
    simpa using (tendsto_const_nhds (x := w)).sub this
  have hle : ∀ᶠ T : ℕ in atTop, w - 2 * Hb / (T : ℝ) ≤ expectedTotal G c σ τ T / T := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [le_div_iff₀ hTpos, sub_mul, div_mul_cancel₀ _ hTpos.ne']
    have h1 := SCG_tele_lower G c σ τ w φ hcond T
    have h2 := (abs_le.1 (SCG_pot_bound (T := T) σ τ φ)).2
    linarith
  have hup : ∀ᶠ T : ℕ in atTop, expectedTotal G c σ τ T / T ≤
      (Finset.univ.sup' Finset.univ_nonempty (fun p : Fin m × Fin n => G.A p.1 p.2) +
        c * Finset.univ.sup' Finset.univ_nonempty (fun p : Fin n × Fin n => G.S p.1 p.2)) := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [div_le_iff₀ hTpos, mul_comm]
    exact SCG_ET_upper G c hc σ τ T
  unfold payoff
  calc w = Filter.liminf (fun T : ℕ => w - 2 * Hb / (T : ℝ)) atTop := hg.liminf_eq.symm
    _ ≤ _ := Filter.liminf_le_liminf hle hg.isBoundedUnder_ge
        (Filter.isCoboundedUnder_ge_of_eventually_le atTop hup)

theorem SCG_payoff_le {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) (c : ℝ) (hc : 0 ≤ c)
    (σ : Strategy1 m n) (τ : Strategy2 m n) (w : ℝ) (φ : Fin n → ℝ)
    (hcond : ∀ t (h : History m n t),
      ∑ i, ∑ j, σ.act t h i * τ.act t h j * (G.A i j + c * G.S (prevAction h) j + φ j) ≤
        w + φ (prevAction h)) :
    payoff G c σ τ ≤ w := by
  set Hb := ∑ k, |φ k|
  have hφ0 : φ 0 ≤ Hb := by
    have := Finset.single_le_sum (f := fun k => |φ k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ 0)
    linarith [le_abs_self (φ 0)]
  have hg : Tendsto (fun T : ℕ => w + 2 * Hb / (T : ℝ)) atTop (𝓝 w) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (2 * Hb)
    simpa using (tendsto_const_nhds (x := w)).add this
  have hle : ∀ᶠ T : ℕ in atTop, expectedTotal G c σ τ T / T ≤ w + 2 * Hb / (T : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [div_le_iff₀ hTpos, add_mul, div_mul_cancel₀ _ hTpos.ne']
    have h1 := SCG_tele_upper G c σ τ w φ hcond T
    have h2 := (abs_le.1 (SCG_pot_bound (T := T) σ τ φ)).1
    linarith
  have hlo : ∀ᶠ T : ℕ in atTop,
      Finset.univ.inf' Finset.univ_nonempty (fun p : Fin m × Fin n => G.A p.1 p.2) ≤
        expectedTotal G c σ τ T / T := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [le_div_iff₀ hTpos, mul_comm]
    exact SCG_ET_lower G c hc σ τ T
  unfold payoff
  calc _ ≤ Filter.liminf (fun T : ℕ => w + 2 * Hb / (T : ℝ)) atTop :=
        Filter.liminf_le_liminf hle (Filter.isBoundedUnder_of_eventually_ge hlo)
          hg.isCoboundedUnder_ge
    _ = w := hg.liminf_eq

section OneShot
theorem expPay_pure_left {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : ι → κ → ℝ) (i : ι) (q : κ → ℝ) :
    BlottoLP.Flow.expPay M (BlottoLP.Flow.pureMixed i) q = ∑ j, q j * M i j := by
  simp [BlottoLP.Flow.expPay, BlottoLP.Flow.pureMixed]

theorem expPay_pure_right {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : ι → κ → ℝ) (p : ι → ℝ) (j : κ) :
    BlottoLP.Flow.expPay M p (BlottoLP.Flow.pureMixed j) = ∑ i, p i * M i j := by
  simp [BlottoLP.Flow.expPay, BlottoLP.Flow.pureMixed]

theorem pureMixed_isMixed {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    BlottoLP.Flow.IsMixed (BlottoLP.Flow.pureMixed a) := by
  refine ⟨fun b => ?_, ?_⟩
  · unfold BlottoLP.Flow.pureMixed; split_ifs <;> norm_num
  · simp [BlottoLP.Flow.pureMixed]

/-- Uniqueness of the saddle value of a one-shot zero-sum game. -/
theorem SCG_saddleValue_unique {ι κ : Type*} [Fintype ι] [Fintype κ] (M : ι → κ → ℝ)
    (v w : ℝ) (hv : IsSaddleValue M v) (hw : IsSaddleValue M w) : v = w := by
  obtain ⟨p, q, ⟨hp, hq, hp1, hq1⟩, rfl⟩ := hv
  obtain ⟨p', q', ⟨hp', hq', hp1', hq1'⟩, rfl⟩ := hw
  have h1 := hq1 q' hq'
  have h2 := hp1' p hp
  have h3 := hq1' q hq
  have h4 := hp1 p' hp'
  linarith

theorem SCG_mixed_of {α : Type*} [Fintype α] {k : ℕ} (g : α ≃ Fin k) (z : Fin k → ℝ)
    (hz : z ∈ stdSimplex ℝ (Fin k)) : BlottoLP.Flow.IsMixed (z ∘ g) := by
  refine ⟨fun x => hz.1 _, ?_⟩
  rw [← hz.2]
  exact g.sum_comp z

theorem SCG_simplex_of {α : Type*} [Fintype α] {k : ℕ} (g : α ≃ Fin k) (z : α → ℝ)
    (hz : BlottoLP.Flow.IsMixed z) : z ∘ g.symm ∈ stdSimplex ℝ (Fin k) := by
  refine ⟨fun x => hz.1 _, ?_⟩
  rw [← hz.2]
  exact g.symm.sum_comp z

/-- Existence of a saddle value for any finite nonempty zero-sum game (von Neumann's minimax
theorem, transported from `AGT.zero_sum_minimax`). -/
theorem SCG_saddleValue_exists {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (M : ι → κ → ℝ) : ∃ v, IsSaddleValue M v := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, Fintype.card ι = a + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  obtain ⟨b, hb⟩ : ∃ b, Fintype.card κ = b + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  let e : ι ≃ Fin (a + 1) := Fintype.equivFinOfCardEq ha
  let f : κ ≃ Fin (b + 1) := Fintype.equivFinOfCardEq hb
  let A : Matrix (Fin (a + 1)) (Fin (b + 1)) ℝ := fun i j => M (e.symm i) (f.symm j)
  obtain ⟨p, hp, q, hq, hpmax, hqmin, -⟩ := AGT.zero_sum_minimax A
  -- the payoff in coordinates
  have key : ∀ (x : ι → ℝ) (y : κ → ℝ),
      BlottoLP.Flow.expPay M x y = (x ∘ e.symm) ⬝ᵥ A.mulVec (y ∘ f.symm) := by
    intro x y
    simp only [BlottoLP.Flow.expPay, dotProduct, Matrix.mulVec, Function.comp, A,
      Finset.mul_sum]
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← f.symm.sum_comp]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have ce : ∀ z : Fin (a + 1) → ℝ, (z ∘ e) ∘ e.symm = z := by
    intro z; funext i; simp
  have cf : ∀ z : Fin (b + 1) → ℝ, (z ∘ f) ∘ f.symm = z := by
    intro z; funext i; simp
  refine ⟨BlottoLP.Flow.expPay M (p ∘ e) (q ∘ f), p ∘ e, q ∘ f,
    ⟨SCG_mixed_of e p hp, SCG_mixed_of f q hq, ?_, ?_⟩, rfl⟩
  · intro σ' hσ'
    rw [key, key, cf, ce]
    exact hpmax _ (SCG_simplex_of e σ' hσ')
  · intro τ' hτ'
    rw [key, key, cf, ce]
    exact hqmin _ (SCG_simplex_of f τ' hτ')


theorem SCG_expPay_le_add {ι κ : Type*} [Fintype ι] [Fintype κ] (M M' : ι → κ → ℝ) (δ : ℝ)
    (hM : ∀ i j, M' i j ≤ M i j + δ) (p : ι → ℝ) (q : κ → ℝ) (hp : BlottoLP.Flow.IsMixed p)
    (hq : BlottoLP.Flow.IsMixed q) :
    BlottoLP.Flow.expPay M' p q ≤ BlottoLP.Flow.expPay M p q + δ := by
  unfold BlottoLP.Flow.expPay
  have hδ : δ = ∑ a, ∑ b, p a * q b * δ := by
    simp only [← Finset.sum_mul, ← Finset.mul_sum, hq.2, hp.2, mul_one, one_mul]
  rw [hδ, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun b _ => ?_)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (hM a b) (mul_nonneg (hp.1 a) (hq.1 b))

/-- Comparison of saddle values: if `M' ≤ M + δ` entrywise then `val M' ≤ val M + δ`. -/
theorem SCG_saddle_le {ι κ : Type*} [Fintype ι] [Fintype κ] (M M' : ι → κ → ℝ) (δ v v' : ℝ)
    (hv : IsSaddleValue M v) (hv' : IsSaddleValue M' v') (hM : ∀ i j, M' i j ≤ M i j + δ) :
    v' ≤ v + δ := by
  obtain ⟨p, q, ⟨hp, hq, hp1, hq1⟩, rfl⟩ := hv
  obtain ⟨p', q', ⟨hp', hq', hp1', hq1'⟩, rfl⟩ := hv'
  have h1 := hq1' q hq
  have h2 := SCG_expPay_le_add M M' δ hM p' q hp' hq
  have h3 := hp1 p' hp'
  linarith

/-- Existence of a solution of the average-cost optimality equation
`w + h(k) = val (base k i j + h j)` for column-shift games whose next state is the column. -/
theorem SCG_acoe {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ} [NeZero n]
    (base : Fin n → ι → Fin n → ℝ) :
    ∃ (w : ℝ) (h : Fin n → ℝ), ∀ k, IsSaddleValue (fun i j => base k i j + h j) (w + h k) := by
  classical
  let V : Fin n → (Fin n → ℝ) → ℝ := fun k x =>
    Classical.choose (SCG_saddleValue_exists (fun i j => base k i j + x j))
  have hV : ∀ k x, IsSaddleValue (fun i j => base k i j + x j) (V k x) := fun k x =>
    Classical.choose_spec (SCG_saddleValue_exists (fun i j => base k i j + x j))
  have hcmp : ∀ k k' (x x' : Fin n → ℝ) (δ : ℝ),
      (∀ i j, base k' i j + x' j ≤ base k i j + x j + δ) → V k' x' ≤ V k x + δ :=
    fun k k' x x' δ h => SCG_saddle_le _ _ δ _ _ (hV k x) (hV k' x') h
  -- uniform bound on differences of the base payoffs
  set Bs : ℝ := 2 * ∑ p : Fin n × ι × Fin n, |base p.1 p.2.1 p.2.2| with hBs
  have hB : ∀ k k' i j, base k' i j ≤ base k i j + Bs := by
    intro k k' i j
    have h1 := Finset.single_le_sum (f := fun p : Fin n × ι × Fin n => |base p.1 p.2.1 p.2.2|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ (k', i, j))
    have h2 := Finset.single_le_sum (f := fun p : Fin n × ι × Fin n => |base p.1 p.2.1 p.2.2|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ (k, i, j))
    simp only at h1 h2
    have := le_abs_self (base k' i j)
    have := neg_abs_le (base k i j)
    linarith
  have hBs0 : 0 ≤ Bs := by
    rw [hBs]; exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun p _ => abs_nonneg _))
  -- Lipschitz in the shift
  have hlip : ∀ k (x x' : Fin n → ℝ), |V k x - V k x'| ≤ dist x x' := by
    intro k x x'
    have hj : ∀ j, |x j - x' j| ≤ dist x x' := fun j => by
      rw [← Real.dist_eq]; exact dist_le_pi_dist x x' j
    rw [abs_le]
    constructor
    · have := hcmp k k x x' (dist x x') (fun i j => by
        have := (abs_le.1 (hj j)).1; linarith)
      linarith
    · have := hcmp k k x' x (dist x x') (fun i j => by
        have := (abs_le.1 (hj j)).2; linarith)
      linarith
  have hVcont : ∀ k, Continuous (V k) := by
    intro k
    refine (LipschitzWith.of_dist_le_mul (K := 1) (fun x x' => ?_)).continuous
    rw [Real.dist_eq]; simpa using hlip k x x'
  -- translation
  have htrans : ∀ k (x : Fin n → ℝ) (a : ℝ), V k (fun j => x j + a) = V k x + a := by
    intro k x a
    apply le_antisymm
    · exact hcmp k k x _ a (fun i j => by linarith)
    · have := hcmp k k (fun j => x j + a) x (-a) (fun i j => by linarith)
      linarith
  -- discounted fixed points
  have hfix : ∀ l : ℝ, 0 ≤ l → l < 1 → ∃ u : Fin n → ℝ, ∀ k, u k = V k (fun j => l * u j) := by
    intro l hl0 hl1
    let F : (Fin n → ℝ) → (Fin n → ℝ) := fun u k => V k (fun j => l * u j)
    have hF : ContractingWith ⟨l, hl0⟩ F := by
      refine ⟨by exact_mod_cast hl1, LipschitzWith.of_dist_le_mul (fun u u' => ?_)⟩
      refine (dist_pi_le_iff (mul_nonneg hl0 dist_nonneg)).2 (fun k => ?_)
      rw [Real.dist_eq]
      refine (hlip k _ _).trans ?_
      refine (dist_pi_le_iff (mul_nonneg hl0 dist_nonneg)).2 (fun j => ?_)
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hl0, ← Real.dist_eq]
      exact mul_le_mul_of_nonneg_left (dist_le_pi_dist u u' j) hl0
    exact ⟨ContractingWith.fixedPoint F hF, fun k =>
      (congrFun (ContractingWith.fixedPoint_isFixedPt (f := F) hF) k).symm⟩
  let lam : ℕ → ℝ := fun N => 1 - 1 / ((N : ℝ) + 2)
  have hlam0 : ∀ N, 0 ≤ lam N := by
    intro N
    have : 1 / ((N : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    simp only [lam]; linarith
  have hlam1 : ∀ N, lam N < 1 := by
    intro N
    have : 0 < 1 / ((N : ℝ) + 2) := by positivity
    simp only [lam]; linarith
  have hlamlim : Tendsto lam atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h3 : Tendsto (fun N : ℕ => ((N : ℝ) + 2)⁻¹) atTop (𝓝 0) := h1.inv_tendsto_atTop
    simpa [lam, one_div] using (tendsto_const_nhds (x := (1 : ℝ))).sub h3
  choose u hu using fun N => hfix (lam N) (hlam0 N) (hlam1 N)
  -- span bound
  have hspan : ∀ N k k', u N k ≤ u N k' + Bs := by
    intro N k k'
    rw [hu N k, hu N k']
    exact hcmp k' k _ _ Bs (fun i j => by linarith [hB k' k i j])
  -- normalized potentials and averages
  let hN : ℕ → Fin n → ℝ := fun N j => u N j - u N 0
  let zN : ℕ → ℝ := fun N => (1 - lam N) * u N 0
  have hzN : ∀ N, |zN N - V 0 0| ≤ Bs := by
    intro N
    have hl0 := hlam0 N
    have hl1 := hlam1 N
    have e0 := hu N 0
    rw [abs_le]
    constructor
    · -- lower bound
      have := hcmp 0 0 (fun j => lam N * u N j) (fun _ => 0) (lam N * (Bs - u N 0))
        (fun i j => by
          have := hspan N 0 j
          have : 0 ≤ lam N * (u N j - u N 0 + Bs) := mul_nonneg hl0 (by linarith)
          nlinarith)
      have e1 : V 0 (fun _ => (0 : ℝ)) = V 0 0 := rfl
      rw [e1, ← e0] at this
      simp only [zN]
      nlinarith
    · have := hcmp 0 0 (fun _ => 0) (fun j => lam N * u N j) (lam N * (u N 0 + Bs))
        (fun i j => by
          have := hspan N j 0
          have : lam N * u N j ≤ lam N * (u N 0 + Bs) := mul_le_mul_of_nonneg_left this hl0
          linarith)
      have e1 : V 0 (fun _ => (0 : ℝ)) = V 0 0 := rfl
      rw [e1, ← e0] at this
      simp only [zN]
      nlinarith
  have hhN : ∀ N j, |hN N j| ≤ Bs := by
    intro N j
    simp only [hN]
    rw [abs_le]
    constructor <;> linarith [hspan N j 0, hspan N 0 j]
  -- the key identity along the sequence
  have hkey : ∀ N k, hN N k + zN N = V k (fun j => lam N * hN N j) := by
    intro N k
    have e := hu N k
    have e2 : (fun j => lam N * u N j) = fun j => lam N * hN N j + lam N * u N 0 := by
      funext j; simp only [hN]; ring
    rw [e2, htrans] at e
    simp only [hN, zN]
    linarith
  -- Bolzano–Weierstrass
  let p : ℕ → (Fin n → ℝ) × ℝ := fun N => (hN N, zN N)
  have hpb : ∀ N, p N ∈ Metric.closedBall (0 : (Fin n → ℝ) × ℝ) (Bs + |V 0 0|) := by
    intro N
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    apply max_le
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun j => ?_)
      rw [Real.norm_eq_abs]
      linarith [hhN N j, abs_nonneg (V 0 0)]
    · show ‖zN N‖ ≤ _
      rw [Real.norm_eq_abs]
      have := hzN N
      have : |zN N| ≤ |zN N - V 0 0| + |V 0 0| := by
        have := abs_add_le (zN N - V 0 0) (V 0 0)
        simpa using this
      linarith
  obtain ⟨⟨hl, wl⟩, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hpb
  refine ⟨wl, hl, fun k => ?_⟩
  have hk1 : Tendsto (fun N => hN (φ N) k + zN (φ N)) atTop (𝓝 (hl k + wl)) := by
    have hfst := (continuous_apply k).continuousAt.tendsto.comp
      ((continuous_fst.tendsto _).comp hlim)
    have hsnd := (continuous_snd.tendsto _).comp hlim
    exact hfst.add hsnd
  have hk2 : Tendsto (fun N => V k (fun j => lam (φ N) * hN (φ N) j)) atTop (𝓝 (V k hl)) := by
    have hl' : Tendsto (fun N => lam (φ N) • hN (φ N)) atTop (𝓝 ((1 : ℝ) • hl)) := by
      have hfst := (continuous_fst.tendsto _).comp hlim
      exact (hlamlim.comp hφ.tendsto_atTop).smul hfst
    rw [one_smul] at hl'
    exact ((hVcont k).tendsto hl).comp hl'
  have heq : hl k + wl = V k hl := by
    refine tendsto_nhds_unique hk1 ?_
    refine hk2.congr (fun N => ?_)
    exact (hkey (φ N) k).symm
  rw [add_comm, heq]
  exact hV k hl

end OneShot

theorem solution {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) (c : ℝ) (hc : 0 ≤ c) :
    ∃ v : ℝ, IsValue G c v := by
  classical
  obtain ⟨w, φ, hacoe⟩ := SCG_acoe (ι := Fin m) (fun k i j => G.A i j + c * G.S k j)
  choose x y hNash hval using hacoe
  let σ : Strategy1 m n := ⟨fun _ h => x (prevAction h), fun _ h => (hNash _).1⟩
  let τ : Strategy2 m n := ⟨fun _ h => y (prevAction h), fun _ h => (hNash _).2.1⟩
  refine ⟨w, σ, τ, ⟨x, fun _ _ => rfl⟩, ⟨y, fun _ _ => rfl⟩, ?_, ?_⟩
  · intro τ'
    refine SCG_payoff_ge G c hc σ τ' w φ (fun t h => ?_)
    have hcol : ∀ j, w + φ (prevAction h) ≤
        ∑ i, x (prevAction h) i * (G.A i j + c * G.S (prevAction h) j + φ j) := by
      intro j
      have := (hNash (prevAction h)).2.2.2 (BlottoLP.Flow.pureMixed j) (pureMixed_isMixed j)
      rw [hval, expPay_pure_right] at this
      exact this
    calc w + φ (prevAction h) = ∑ j, τ'.act t h j * (w + φ (prevAction h)) := by
          rw [← Finset.sum_mul, (τ'.act_mem t h).2, one_mul]
      _ ≤ ∑ j, τ'.act t h j * ∑ i, x (prevAction h) i *
            (G.A i j + c * G.S (prevAction h) j + φ j) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hcol j)
            ((τ'.act_mem t h).1 j))
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [σ]
          ring
  · intro σ'
    refine SCG_payoff_le G c hc σ' τ w φ (fun t h => ?_)
    have hrow : ∀ i, ∑ j, y (prevAction h) j * (G.A i j + c * G.S (prevAction h) j + φ j) ≤
        w + φ (prevAction h) := by
      intro i
      have := (hNash (prevAction h)).2.2.1 (BlottoLP.Flow.pureMixed i) (pureMixed_isMixed i)
      rw [hval, expPay_pure_left] at this
      exact this
    calc _ = ∑ i, σ'.act t h i * ∑ j, y (prevAction h) j *
            (G.A i j + c * G.S (prevAction h) j + φ j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [τ]
          ring
      _ ≤ ∑ i, σ'.act t h i * (w + φ (prevAction h)) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i)
            ((σ'.act_mem t h).1 i))
      _ = w + φ (prevAction h) := by
          rw [← Finset.sum_mul, (σ'.act_mem t h).2, one_mul]
