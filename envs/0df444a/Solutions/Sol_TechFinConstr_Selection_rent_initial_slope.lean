-- Prove2me | solution 1 for TechFinConstr.Selection.rent_initial_slope
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:04:27.67321+00:00
-- url     : https://prove2.me/submissions/45749692-4524-42d8-b1a8-c1e59546d69e

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace P6Aux
open Finset hiding expect
open TechFinConstr.Selection

theorem telesc (m : ℕ) (s : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∑ k : Fin m, (if k.succ ≤ i then s k.succ - s k.castSucc else 0) = s i - s 0 := by
  induction i using Fin.induction with
  | zero =>
    simp only [Fin.le_zero_iff, Fin.succ_ne_zero, if_false, sum_const_zero, sub_self]
  | succ j ih =>
    have h : ∀ k : Fin m, (if k.succ ≤ j.succ then s k.succ - s k.castSucc else 0) =
        (if k.succ ≤ j.castSucc then s k.succ - s k.castSucc else 0) +
        (if j = k then s k.succ - s k.castSucc else 0) := by
      intro k
      by_cases h1 : k < j
      · have h2 : k.succ ≤ j.succ := by simp only [Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.val_succ, Fin.val_castSucc] at *; omega
        have h3 : k.succ ≤ j.castSucc := by simp only [Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.val_succ, Fin.val_castSucc] at *; omega
        have h4 : j ≠ k := by intro h; subst h; exact lt_irrefl _ h1
        simp [h2, h3, h4]
      · by_cases h5 : j = k
        · subst h5
          have h3 : ¬ j.succ ≤ j.castSucc := by simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]; omega
          simp [h3]
        · have h2 : ¬ k.succ ≤ j.succ := by
            simp only [Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at *; omega
          have h3 : ¬ k.succ ≤ j.castSucc := by
            simp only [Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at *; omega
          simp [h2, h3, h5]
    rw [sum_congr rfl (fun k _ => h k), sum_add_distrib, ih, sum_ite_eq]
    simp only [mem_univ, if_true]
    ring

theorem abel (m : ℕ) (w s : Fin (m + 1) → ℝ) :
    ∑ i, w i * s i = s 0 * ∑ i, w i +
      ∑ k : Fin m, (s k.succ - s k.castSucc) * tail w k.succ := by
  have h1 : ∀ i, w i * s i = s 0 * w i +
      ∑ k : Fin m, (if k.succ ≤ i then (s k.succ - s k.castSucc) * w i else 0) := by
    intro i
    have := telesc m s i
    have h2 : ∑ k : Fin m, (if k.succ ≤ i then (s k.succ - s k.castSucc) * w i else 0) =
        (∑ k : Fin m, (if k.succ ≤ i then s k.succ - s k.castSucc else 0)) * w i := by
      rw [sum_mul]; apply sum_congr rfl; intro k _; split_ifs <;> simp
    rw [h2, this]; ring
  rw [sum_congr rfl (fun i _ => h1 i), sum_add_distrib, ← mul_sum, sum_comm]
  congr 1
  apply sum_congr rfl; intro k _
  simp only [tail, sum_filter, mul_sum]
  apply sum_congr rfl; intro i _
  split_ifs <;> simp


variable {n : ℕ}

def Adm (E : Economy n) (s : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ s i) ∧ (∀ i : Fin n, s i.castSucc ≤ s i.succ) ∧
  (∀ i : Fin n, E.x i.castSucc - s i.castSucc ≤ E.x i.succ - s i.succ)

theorem expect_comb (w s t : Fin (n + 1) → ℝ) (a b : ℝ) :
    expect w (fun i => a * s i + b * t i) = a * expect w s + b * expect w t := by
  simp only [expect, mul_add, sum_add_distrib, mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intro i _ <;> ring

theorem expect_sub_eq (w a b : Fin (n + 1) → ℝ) :
    expect w (a - b) = expect w a - expect w b := by
  simp only [expect, Pi.sub_apply, mul_sub, sum_sub_distrib]

theorem expect_nonneg {E : Economy n} (hE : E.Standing) {s : Fin (n + 1) → ℝ}
    (hs : ∀ i, 0 ≤ s i) : 0 ≤ expect E.q s :=
  sum_nonneg (fun i _ => mul_nonneg (hE.2.2.2.1 i).le (hs i))

theorem adm_comb {E : Economy n} (hE : E.Standing) {s t : Fin (n + 1) → ℝ}
    (hs : Adm E s) (ht : Adm E t) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    Adm E (fun i => a * s i + b * t i) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact add_nonneg (mul_nonneg ha (hs.1 i)) (mul_nonneg hb (ht.1 i))
  · have h1 := hs.2.1 i; have h2 := ht.2.1 i
    have e1 := mul_le_mul_of_nonneg_left h1 ha
    have e2 := mul_le_mul_of_nonneg_left h2 hb
    linarith
  · have h3 := hs.2.2 i; have h4 := ht.2.2 i
    have hx : E.x i.castSucc < E.x i.succ := hE.2.2.1 ((Fin.castSucc_lt_succ (i := i)))
    have e1 : a * (s i.succ - s i.castSucc) ≤ a * (E.x i.succ - E.x i.castSucc) :=
      mul_le_mul_of_nonneg_left (by linarith) ha
    have e2 : b * (t i.succ - t i.castSucc) ≤ b * (E.x i.succ - E.x i.castSucc) :=
      mul_le_mul_of_nonneg_left (by linarith) hb
    have e3 : (a + b) * (E.x i.succ - E.x i.castSucc) ≤ E.x i.succ - E.x i.castSucc := by
      have := mul_le_mul_of_nonneg_right hab (by linarith : (0:ℝ) ≤ E.x i.succ - E.x i.castSucc)
      linarith
    nlinarith

theorem tail_sub (p q : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    tail (p - q) j = tail p j - tail q j := by
  simp only [tail, Pi.sub_apply, sum_sub_distrib]

theorem B_eq {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p)
    (s : Fin (n + 1) → ℝ) :
    expect p s - expect E.q s =
      ∑ k : Fin n, (s k.succ - s k.castSucc) * (tail p k.succ - tail E.q k.succ) := by
  unfold expect
  rw [abel n p s, abel n E.q s, hp.2.1, hE.2.2.2.2.1]
  simp only [mul_sub, sum_sub_distrib]
  ring

theorem pi_eq {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p) :
    E.piE = ∑ k : Fin n, (E.x k.succ - E.x k.castSucc) * (tail p k.succ - tail E.q k.succ) := by
  rw [← hp.2.2.1]; exact B_eq hE hp E.x

theorem Eq_eq {E : Economy n} (hE : E.Standing) (s : Fin (n + 1) → ℝ) :
    expect E.q s = s 0 + ∑ k : Fin n, (s k.succ - s k.castSucc) * tail E.q k.succ := by
  unfold expect
  rw [abel n E.q s, hE.2.2.2.2.1, mul_one]

theorem td_nonneg {E : Economy n} {p : Fin (n + 1) → ℝ} (hp : InP E p) (j : Fin (n + 1)) :
    0 ≤ tail p j - tail E.q j := sub_nonneg.2 (hp.2.2.2.1 j)

theorem tq_pos {E : Economy n} (hE : E.Standing) (j : Fin (n + 1)) : 0 < tail E.q j :=
  sum_pos (fun i _ => hE.2.2.2.1 i) ⟨j, by simp⟩

theorem Phi_zero {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p) :
    Phi E p 0 = 0 := by
  have : tail (p - E.q) 0 = 0 := by
    simp [tail, sum_sub_distrib, hp.2.1, hE.2.2.2.2.1]
  simp [Phi, this]

theorem PhiStar_nonneg {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p) :
    0 ≤ PhiStar E p := by
  have := le_sup' (Phi E p) (mem_univ 0)
  rw [Phi_zero hE hp] at this
  exact this

theorem td_eq {E : Economy n} (hE : E.Standing) (p : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    tail p j - tail E.q j = Phi E p j * tail E.q j := by
  rw [Phi, tail_sub, div_mul_cancel₀ _ (tq_pos hE _).ne']

theorem B_le {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p)
    {s : Fin (n + 1) → ℝ} (hs : Adm E s) :
    expect p s - expect E.q s ≤ PhiStar E p * expect E.q s := by
  rw [B_eq hE hp s, Eq_eq hE s, mul_add, mul_sum]
  have h1 : 0 ≤ PhiStar E p * s 0 := mul_nonneg (PhiStar_nonneg hE hp) (hs.1 0)
  have h2 : ∑ k : Fin n, (s k.succ - s k.castSucc) * (tail p k.succ - tail E.q k.succ) ≤
      ∑ k : Fin n, PhiStar E p * ((s k.succ - s k.castSucc) * tail E.q k.succ) := by
    apply sum_le_sum; intro k _
    rw [td_eq hE p]
    have hP : Phi E p k.succ ≤ PhiStar E p := le_sup' (Phi E p) (mem_univ k.succ)
    have hd : 0 ≤ s k.succ - s k.castSucc := sub_nonneg.2 (hs.2.1 k)
    have := mul_nonneg (mul_nonneg hd (tq_pos hE k.succ).le) (sub_nonneg.2 hP)
    nlinarith
  linarith

theorem tranche_adm {E : Economy n} (hE : E.Standing) (k : Fin n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ E.x k.succ - E.x k.castSucc) :
    Adm E (fun i => if k.succ ≤ i then t else 0) := by
  refine ⟨fun i => by dsimp only; split_ifs <;> linarith, fun i => ?_, fun i => ?_⟩
  · dsimp only
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso; apply h2
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] at *; omega
    · exact ht0
    · exact le_rfl
  · have hx : E.x i.castSucc < E.x i.succ := hE.2.2.1 ((Fin.castSucc_lt_succ (i := i)))
    dsimp only
    split_ifs with h1 h2
    · linarith
    · exfalso; apply h2
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] at *; omega
    · have : k = i := by
        apply Fin.ext
        simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] at *; omega
      subst this; linarith
    · linarith

theorem expect_tranche (w : Fin (n + 1) → ℝ) (k : Fin n) (t : ℝ) :
    expect w (fun i => if k.succ ≤ i then t else 0) = t * tail w k.succ := by
  simp only [expect, tail, sum_filter, mul_sum]
  apply sum_congr rfl; intro i _; split_ifs <;> ring

theorem opt_adm {E : Economy n} {p : Fin (n + 1) → ℝ} {c : ℝ} {s : Fin (n + 1) → ℝ}
    (hs : IsOptimalContract E p c s) : Adm E s ∧ c ≤ expect p s - expect E.q s :=
  ⟨⟨hs.1.2.2.1, hs.1.2.2.2.1, hs.1.2.2.2.2⟩, by linarith [hs.1.1]⟩

theorem opt_le {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} {c : ℝ} (hc : 0 < c)
    {s : Fin (n + 1) → ℝ} (hs : IsOptimalContract E p c s) {s' : Fin (n + 1) → ℝ}
    (hs' : Adm E s') (hB : c ≤ expect p s' - expect E.q s') :
    expect E.q s ≤ expect E.q s' := by
  set b := expect p s' - expect E.q s' with hb
  have hbpos : 0 < b := lt_of_lt_of_le hc hB
  set t := c / b with ht
  have ht0 : 0 ≤ t := div_nonneg hc.le hbpos.le
  have ht1 : t ≤ 1 := (div_le_one hbpos).2 hB
  have htb : t * b = c := div_mul_cancel₀ c hbpos.ne'
  have hadm := adm_comb hE hs' hs' ht0 le_rfl (by linarith)
  have hq'' := expect_comb E.q s' s' t 0
  have hp'' := expect_comb p s' s' t 0
  have hEq0 := expect_nonneg hE hs'.1
  have hkey : t * expect p s' - t * expect E.q s' = c := by rw [← mul_sub]; exact htb
  have hfeas : Feasible E p c (fun i => t * s' i + 0 * s' i) := by
    refine ⟨?_, ?_, hadm.1, hadm.2.1, hadm.2.2⟩
    · rw [hq'', hp'']; linarith
    · rw [hp'']; nlinarith
  have h1 := hs.2 _ hfeas
  rw [expect_sub_eq, expect_sub_eq, hp''] at h1
  have h2 := hs.1.1
  have h3 : t * expect E.q s' ≤ expect E.q s' := by nlinarith
  linarith

theorem cont_expect (w : Fin (n + 1) → ℝ) :
    Continuous (fun s : Fin (n + 1) → ℝ => expect w s) := by
  unfold expect
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))

theorem x_nonneg {E : Economy n} (hE : E.Standing) (i : Fin (n + 1)) : 0 ≤ E.x i := by
  rw [← hE.2.1]; exact hE.2.2.1.monotone (Fin.zero_le i)

theorem exists_opt {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p)
    {c : ℝ} (hc : c ≤ E.piE) : ∃ s, IsOptimalContract E p c s := by
  set M := expect p E.x with hM
  let K : Set (Fin (n + 1) → ℝ) :=
    {s | expect E.q s ≤ expect p s - c} ∩ {s | 0 ≤ expect p s - c} ∩ (⋂ i, {s | 0 ≤ s i}) ∩
    (⋂ i : Fin n, {s | s i.castSucc ≤ s i.succ}) ∩
    (⋂ i : Fin n, {s | E.x i.castSucc - s i.castSucc ≤ E.x i.succ - s i.succ}) ∩ {s | s 0 ≤ M}
  have hmemK : ∀ s, s ∈ K ↔ Feasible E p c s ∧ s 0 ≤ M := by
    intro s
    simp only [K, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Feasible, ge_iff_le]
    tauto
  have hEqx : 0 ≤ expect E.q E.x := expect_nonneg hE (x_nonneg hE)
  have hM0 : 0 ≤ M := sum_nonneg (fun i _ => mul_nonneg (hp.1 i) (x_nonneg hE i))
  have hpix := hp.2.2.1
  have hxF : Feasible E p c E.x := by
    refine ⟨by linarith, by linarith, x_nonneg hE, fun i => ?_, fun i => ?_⟩
    · exact hE.2.2.1.monotone (Fin.castSucc_le_succ i)
    · simp
  have hxK : E.x ∈ K := (hmemK _).2 ⟨hxF, by rw [hE.2.1]; linarith⟩
  have hclosed : IsClosed K := by
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_) ?_
    · exact isClosed_le (cont_expect _) ((cont_expect _).sub continuous_const)
    · exact isClosed_le continuous_const ((cont_expect _).sub continuous_const)
    · exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_iInter fun i => isClosed_le (continuous_apply _) (continuous_apply _)
    · exact isClosed_iInter fun i => isClosed_le (continuous_const.sub (continuous_apply _))
        (continuous_const.sub (continuous_apply _))
    · exact isClosed_le (continuous_apply _) continuous_const
  have hbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin (n + 1) → ℝ))
      (r := M + E.x (Fin.last n))).subset ?_
    intro s hs
    obtain ⟨hF, hs0⟩ := (hmemK s).1 hs
    have hr : 0 ≤ M + E.x (Fin.last n) := by
      have := x_nonneg hE (Fin.last n); linarith
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr]
    intro i
    have hmon : Monotone (fun i => E.x i - s i) := Fin.monotone_iff_le_succ.2 hF.2.2.2.2
    have h1 := hmon (Fin.zero_le i)
    have h2 := hE.2.2.1.monotone (Fin.le_last i)
    have h3 := hF.2.2.1 i
    simp only at h1
    rw [Real.norm_eq_abs, abs_le]
    rw [hE.2.1] at h1
    constructor <;> linarith
  have hK : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  obtain ⟨s, hsK, hmin⟩ := hK.exists_isMinOn ⟨E.x, hxK⟩ (cont_expect p).continuousOn
  obtain ⟨hsF, hs0⟩ := (hmemK s).1 hsK
  refine ⟨s, hsF, fun s' hs' => ?_⟩
  rw [expect_sub_eq, expect_sub_eq]
  suffices expect p s ≤ expect p s' by linarith
  by_cases h : s' 0 ≤ M
  · exact hmin ((hmemK s').2 ⟨hs', h⟩)
  · replace h := not_le.1 h
    have hmon : Monotone s' := Fin.monotone_iff_le_succ.2 hs'.2.2.2.1
    have h1 : s' 0 ≤ expect p s' := by
      have : ∑ i, p i * s' 0 ≤ ∑ i, p i * s' i :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmon (Fin.zero_le i)) (hp.1 i)
      rw [← sum_mul, hp.2.1, one_mul] at this
      exact this
    have h2 : expect p s ≤ expect p E.x := hmin hxK
    linarith


theorem tail_last (w : Fin (n + 1) → ℝ) : tail w (Fin.last n) = w (Fin.last n) := by
  simp only [tail, Fin.last_le_iff, sum_filter, sum_ite_eq', mem_univ, if_true]

theorem tail_one (w : Fin (n + 1) → ℝ) (k0 : Fin n) (hk0 : k0.val = 0) :
    tail w k0.succ = ∑ i, w i - w 0 := by
  have hA : ∀ k : Fin n, k0.succ ≤ k.succ :=
    fun k => Fin.succ_le_succ_iff.2 (Fin.le_iff_val_le_val.2 (by omega))
  have hB : ¬ k0.succ ≤ (0 : Fin (n + 1)) := by
    rw [Fin.le_zero_iff]; exact Fin.succ_ne_zero _
  simp only [tail, sum_filter]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := w)]
  simp only [hA, hB, if_true, if_false]
  ring

theorem phi_nonneg_iff {E : Economy n} (hE : E.Standing) (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    0 ≤ phi E p i ↔ E.q i ≤ p i := by
  rw [phi, le_div_iff₀ (hE.2.2.2.1 i), zero_mul, sub_nonneg]

theorem phi_pos_iff {E : Economy n} (hE : E.Standing) (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    0 < phi E p i ↔ E.q i < p i := by
  rw [phi, lt_div_iff₀ (hE.2.2.2.1 i), zero_mul, sub_pos]

theorem lemmaA1 {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p) :
    p 0 < E.q 0 ∧ E.q (Fin.last n) ≤ p (Fin.last n) := by
  have hlast : E.q (Fin.last n) ≤ p (Fin.last n) := by
    have := hp.2.2.2.1 (Fin.last n); rwa [tail_last, tail_last] at this
  refine ⟨?_, hlast⟩
  by_contra h
  replace h := not_lt.1 h
  obtain ⟨m, hinc, hdec⟩ := hp.2.2.2.2.2
  have hall : ∀ i, E.q i ≤ p i := by
    intro i
    rw [← phi_nonneg_iff hE]
    rcases le_total i m with him | hmi
    · exact le_trans ((phi_nonneg_iff hE p 0).2 h) (hinc 0 i (Fin.zero_le _) him)
    · exact le_trans ((phi_nonneg_iff hE p _).2 hlast) (hdec i (Fin.last n) hmi (Fin.le_last _))
  have hz := (sum_eq_zero_iff_of_nonneg (s := univ) (f := fun i => p i - E.q i)
    (fun i _ => sub_nonneg.2 (hall i))).1 (by rw [sum_sub_distrib, hp.2.1, hE.2.2.2.2.1]; ring)
  obtain ⟨j, hj⟩ := hp.2.2.2.2.1
  have : tail p j = tail E.q j := by
    unfold tail; apply sum_congr rfl; intro i _
    have := hz i (mem_univ _); linarith
  linarith

theorem td_pos_of {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p)
    (j : Fin (n + 1)) (hj : E.q j < p j) : 0 < tail p j - tail E.q j := by
  have hlast := (lemmaA1 hE hp).2
  obtain ⟨m, hinc, hdec⟩ := hp.2.2.2.2.2
  rw [← tail_sub]
  unfold tail
  have hnn : ∀ i ∈ univ.filter (fun i => j ≤ i), 0 ≤ (p - E.q) i := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [Pi.sub_apply, sub_nonneg]
    rw [← phi_nonneg_iff hE]
    rcases le_total i m with him | hmi
    · exact le_trans ((phi_pos_iff hE p j).2 hj).le (hinc j i hi him)
    · exact le_trans ((phi_nonneg_iff hE p _).2 hlast) (hdec i (Fin.last n) hmi (Fin.le_last _))
  have := single_le_sum hnn (mem_filter.2 ⟨mem_univ j, le_rfl⟩)
  simp only [Pi.sub_apply] at this ⊢
  linarith

theorem PhiStar_pos {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p) :
    0 < PhiStar E p := by
  have hn := hE.1
  set k0 : Fin n := ⟨0, by omega⟩
  have h1 : 0 < Phi E p k0.succ := by
    rw [Phi, tail_sub]
    apply div_pos _ (tq_pos hE _)
    rw [tail_one p k0 rfl, tail_one E.q k0 rfl, hp.2.1, hE.2.2.2.2.1]
    have := (lemmaA1 hE hp).1; linarith
  exact lt_of_lt_of_le h1 (le_sup' (Phi E p) (mem_univ _))

/-- upper bound of an optimal contract's rent by a single partial tranche -/
theorem rent_le_tranche {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ}
    {c : ℝ} (hc : 0 < c) (k : Fin n) (htd : 0 < tail p k.succ - tail E.q k.succ)
    (hck : c ≤ (E.x k.succ - E.x k.castSucc) * (tail p k.succ - tail E.q k.succ))
    {s : Fin (n + 1) → ℝ} (hs : IsOptimalContract E p c s) :
    expect E.q s * (tail p k.succ - tail E.q k.succ) ≤ c * tail E.q k.succ := by
  set td := tail p k.succ - tail E.q k.succ
  set t := c / td with ht
  have ht0 : 0 ≤ t := div_nonneg hc.le htd.le
  have htdx : t ≤ E.x k.succ - E.x k.castSucc := (div_le_iff₀ htd).2 hck
  have htt : t * td = c := div_mul_cancel₀ c htd.ne'
  have hadm := tranche_adm hE k ht0 htdx
  have hB : c ≤ expect p (fun i => if k.succ ≤ i then t else 0) -
      expect E.q (fun i => if k.succ ≤ i then t else 0) := by
    rw [expect_tranche, expect_tranche, ← mul_sub]; exact htt.ge
  have h := opt_le hE hc hs hadm hB
  rw [expect_tranche] at h
  have := mul_le_mul_of_nonneg_right h htd.le
  calc expect E.q s * td ≤ t * tail E.q k.succ * td := this
    _ = c * tail E.q k.succ := by rw [mul_right_comm, htt]

theorem rent_eq {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} {c : ℝ} (hc : 0 < c)
    {s : Fin (n + 1) → ℝ} (hs : IsOptimalContract E p c s) :
    expect E.q s = agencyRent E p c := by
  unfold agencyRent
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨s, hs, rfl⟩, ?_⟩
  rintro _ ⟨s2, hs2, rfl⟩
  exact opt_le hE hc hs (opt_adm hs2).1 (opt_adm hs2).2

theorem rent_le {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p)
    {c : ℝ} (hc : 0 < c) (hcπ : c ≤ E.piE) {s' : Fin (n + 1) → ℝ} (hs' : Adm E s')
    (hB : c ≤ expect p s' - expect E.q s') : agencyRent E p c ≤ expect E.q s' := by
  obtain ⟨s, hs⟩ := exists_opt hE hp hcπ
  rw [← rent_eq hE hc hs]
  exact opt_le hE hc hs hs' hB

/-- initial slope: for small `c`, the rent is `c / Φ*(p)` -/
theorem init_slope {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p) :
    ∃ c₁, 0 < c₁ ∧ c₁ ≤ E.piE ∧ ∀ c, 0 < c → c ≤ c₁ → ∀ s, IsOptimalContract E p c s →
      expect E.q s * PhiStar E p = c := by
  have hpos := PhiStar_pos hE hp
  obtain ⟨j, -, hj⟩ := exists_mem_eq_sup' (univ_nonempty (α := Fin (n + 1))) (Phi E p)
  have hj' : PhiStar E p = Phi E p j := hj
  have hj0 : j ≠ 0 := by
    intro h; rw [h, Phi_zero hE hp] at hj'; linarith
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hj0
  have htdeq := td_eq hE p k.succ
  rw [← hj'] at htdeq
  have htq := tq_pos hE k.succ
  have htd : 0 < tail p k.succ - tail E.q k.succ := by rw [htdeq]; positivity
  have hdx : 0 < E.x k.succ - E.x k.castSucc :=
    sub_pos.2 (hE.2.2.1 (Fin.castSucc_lt_succ (i := k)))
  refine ⟨min ((E.x k.succ - E.x k.castSucc) * (tail p k.succ - tail E.q k.succ)) E.piE,
    lt_min (mul_pos hdx htd) hE.2.2.2.2.2, min_le_right _ _, ?_⟩
  intro c hc hc1 s hs
  have hcπ : c ≤ E.piE := le_trans hc1 (min_le_right _ _)
  have hck := le_trans hc1 (min_le_left _ _)
  have hup := rent_le_tranche hE hc k htd hck hs
  rw [htdeq] at hup
  have hlo := le_trans (opt_adm hs).2 (B_le hE hp (opt_adm hs).1)
  have : expect E.q s * PhiStar E p ≤ c := by
    have := hup; rw [← mul_assoc] at this; exact le_of_mul_le_mul_right this htq
  linarith


theorem td_zero_of_iota_one {E : Economy n} {p : Fin (n + 1) → ℝ} (hp : InP E p)
    (h1 : (iotaBar E p).val = 1) (k : Fin n) (hk : k.val ≠ 0) :
    tail p k.succ - tail E.q k.succ = 0 := by
  apply le_antisymm _ (td_nonneg hp _)
  rw [← tail_sub]
  unfold tail
  apply sum_nonpos
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi
  simp only [Pi.sub_apply, sub_nonpos]
  by_contra h
  replace h := not_le.1 h
  have hle : id i ≤ iotaBar E p := le_sup (f := id) (mem_filter.2 ⟨mem_univ i, h⟩)
  have := Fin.le_iff_val_le_val.1 hle
  have := Fin.le_iff_val_le_val.1 hi
  simp only [id, Fin.val_succ] at *
  omega

theorem rent_one {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p)
    (h1 : (iotaBar E p).val = 1) (k0 : Fin n) (hk0 : k0.val = 0) :
    E.piE = (E.x k0.succ - E.x k0.castSucc) * (tail p k0.succ - tail E.q k0.succ) ∧
    PhiStar E p = Phi E p k0.succ ∧
    ∀ c, 0 < c → c ≤ E.piE → ∀ s, IsOptimalContract E p c s →
      expect E.q s * PhiStar E p = c := by
  have hz : ∀ k : Fin n, k ≠ k0 → tail p k.succ - tail E.q k.succ = 0 := by
    intro k hk
    exact td_zero_of_iota_one hp h1 k (fun h => hk (Fin.ext (by omega)))
  have hpi : E.piE = (E.x k0.succ - E.x k0.castSucc) * (tail p k0.succ - tail E.q k0.succ) := by
    rw [pi_eq hE hp]
    apply sum_eq_single k0 (fun k _ hk => by rw [hz k hk, mul_zero]) (by simp)
  have hdx : 0 < E.x k0.succ - E.x k0.castSucc :=
    sub_pos.2 (hE.2.2.1 (Fin.castSucc_lt_succ (i := k0)))
  have htd : 0 < tail p k0.succ - tail E.q k0.succ := by
    have := td_nonneg hp k0.succ
    rcases this.lt_or_eq with h | h
    · exact h
    · have := hE.2.2.2.2.2; rw [hpi, ← h, mul_zero] at this; exact absurd this (lt_irrefl _)
  have hΦ : PhiStar E p = Phi E p k0.succ := by
    apply le_antisymm _ (le_sup' _ (mem_univ _))
    have hP0 : 0 ≤ Phi E p k0.succ := by
      rw [Phi, tail_sub]; exact div_nonneg htd.le (tq_pos hE _).le
    apply sup'_le
    intro j _
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [Phi_zero hE hp]; exact hP0
    · by_cases hk : k = k0
      · rw [hk]
      · rw [Phi, tail_sub, hz k hk, zero_div]; exact hP0
  refine ⟨hpi, hΦ, ?_⟩
  intro c hc hcπ s hs
  have hup := rent_le_tranche hE hc k0 htd (hpi ▸ hcπ) hs
  have htdeq := td_eq hE p k0.succ
  rw [← hΦ] at htdeq
  rw [htdeq] at hup
  have htq := tq_pos hE k0.succ
  have hlo := le_trans (opt_adm hs).2 (B_le hE hp (opt_adm hs).1)
  have : expect E.q s * PhiStar E p ≤ c := by
    have := hup; rw [← mul_assoc] at this; exact le_of_mul_le_mul_right this htq
  linarith

theorem pair_le_sum (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) {a b : Fin n} (hab : a ≠ b) :
    f a + f b ≤ ∑ i, f i := by
  rw [← sum_pair hab]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hf i)

/-- near `c = π`, a contract must nearly fill tranches `k0` and `ι`. -/
theorem near_pi {E : Economy n} (hE : E.Standing) {p : Fin (n + 1) → ℝ} (hp : InP E p)
    (k0 ι : Fin n) (hι : ι ≠ k0) (h0 : 0 < tail p k0.succ - tail E.q k0.succ)
    (hι' : 0 < tail p ι.succ - tail E.q ι.succ) :
    ∃ K, 0 < K ∧ ∀ s c, Adm E s → c ≤ expect p s - expect E.q s →
      (E.x k0.succ - E.x k0.castSucc) * tail E.q k0.succ +
        (E.x ι.succ - E.x ι.castSucc) * tail E.q ι.succ - K * (E.piE - c) ≤ expect E.q s := by
  set a0 := tail p k0.succ - tail E.q k0.succ
  set aι := tail p ι.succ - tail E.q ι.succ
  have hq0 := tq_pos hE k0.succ
  have hqι := tq_pos hE ι.succ
  refine ⟨tail E.q k0.succ / a0 + tail E.q ι.succ / aι, by positivity, ?_⟩
  intro s c hs hc
  set K := tail E.q k0.succ / a0 + tail E.q ι.succ / aι
  have hd : ∀ k : Fin n, 0 ≤ s k.succ - s k.castSucc := fun k => sub_nonneg.2 (hs.2.1 k)
  have he : ∀ k : Fin n, 0 ≤ (E.x k.succ - E.x k.castSucc) - (s k.succ - s k.castSucc) :=
    fun k => by have := hs.2.2 k; linarith
  -- lower bound on E_q s
  have hEq : (s k0.succ - s k0.castSucc) * tail E.q k0.succ +
      (s ι.succ - s ι.castSucc) * tail E.q ι.succ ≤ expect E.q s := by
    rw [Eq_eq hE s]
    have := pair_le_sum (fun k => (s k.succ - s k.castSucc) * tail E.q k.succ)
      (fun k => mul_nonneg (hd k) (tq_pos hE _).le) hι.symm
    have := hs.1 0
    try simp only at *
    linarith
  -- upper bound on the slack
  have hslack : ((E.x k0.succ - E.x k0.castSucc) - (s k0.succ - s k0.castSucc)) * a0 +
      ((E.x ι.succ - E.x ι.castSucc) - (s ι.succ - s ι.castSucc)) * aι ≤ E.piE - c := by
    have hdiff : E.piE - (expect p s - expect E.q s) = ∑ k : Fin n,
        ((E.x k.succ - E.x k.castSucc) - (s k.succ - s k.castSucc)) *
          (tail p k.succ - tail E.q k.succ) := by
      rw [pi_eq hE hp, B_eq hE hp s, ← sum_sub_distrib]
      apply sum_congr rfl; intro k _; ring
    have := pair_le_sum (fun k => ((E.x k.succ - E.x k.castSucc) - (s k.succ - s k.castSucc)) *
          (tail p k.succ - tail E.q k.succ))
      (fun k => mul_nonneg (he k) (td_nonneg hp _)) hι.symm
    try simp only at this
    linarith
  set e0 := (E.x k0.succ - E.x k0.castSucc) - (s k0.succ - s k0.castSucc)
  set eι := (E.x ι.succ - E.x ι.castSucc) - (s ι.succ - s ι.castSucc)
  have he0 : 0 ≤ e0 := he k0
  have heι : 0 ≤ eι := he ι
  have h1 : e0 * tail E.q k0.succ ≤ K * (e0 * a0) := by
    have : e0 * tail E.q k0.succ = tail E.q k0.succ / a0 * (e0 * a0) := by
      field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg he0 h0.le)
    have : 0 ≤ tail E.q ι.succ / aι := by positivity
    linarith
  have h2 : eι * tail E.q ι.succ ≤ K * (eι * aι) := by
    have : eι * tail E.q ι.succ = tail E.q ι.succ / aι * (eι * aι) := by
      field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg heι hι'.le)
    have : 0 ≤ tail E.q k0.succ / a0 := by positivity
    linarith
  have hK : 0 ≤ K := by positivity
  have h3 : K * (e0 * a0 + eι * aι) ≤ K * (E.piE - c) := mul_le_mul_of_nonneg_left hslack hK
  have h4 : (E.x k0.succ - E.x k0.castSucc) * tail E.q k0.succ +
      (E.x ι.succ - E.x ι.castSucc) * tail E.q ι.succ =
      (s k0.succ - s k0.castSucc) * tail E.q k0.succ + (s ι.succ - s ι.castSucc) * tail E.q ι.succ
      + e0 * tail E.q k0.succ + eι * tail E.q ι.succ := by
    simp only [e0, eι]; ring
  nlinarith

end P6Aux

open TechFinConstr.Selection P6Aux

theorem solution {n : ℕ} (E : Economy n) (hE : E.Standing)
    (p : Fin (n + 1) → ℝ) (hp : InP E p) :
    ∃ c₁, 0 < c₁ ∧ c₁ ≤ E.piE ∧
      ∀ c, 0 < c → c ≤ c₁ →
        (∃ s, IsOptimalContract E p c s) ∧
        ∀ s, IsOptimalContract E p c s → expect E.q s = c / PhiStar E p := by
  obtain ⟨c₁, h0, h1, h⟩ := init_slope hE hp
  have hpos := PhiStar_pos hE hp
  refine ⟨c₁, h0, h1, fun c hc hcc => ⟨exists_opt hE hp (le_trans hcc h1), fun s hs => ?_⟩⟩
  rw [eq_div_iff hpos.ne']
  exact h c hc hcc s hs
