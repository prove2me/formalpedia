-- Prove2me | solution 1 for UniformPatrol.Star.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:00:37.859981+00:00
-- url     : https://prove2.me/submissions/0077faac-9c2a-40a2-89c4-ff43d13d8158

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model


namespace UPSol
open UniformPatrol.Star

/-- Backward survival pair: (survival from the centre, survival from a non-attacked end). -/
def sv (n : ℕ) (p s : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 1)
  | t + 1 => ((1 - (n : ℝ) * p) * (sv n p s t).1 + ((n : ℝ) - 1) * p * (sv n p s t).2,
              s * (sv n p s t).1 + (1 - s) * (sv n p s t).2)

/-- Forward sub-probability pair: (mass at centre, mass at non-attacked ends). -/
def fw (n : ℕ) (p s : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | t + 1 => ((1 - (n : ℝ) * p) * (fw n p s t).1 + s * (fw n p s t).2,
              ((n : ℝ) - 1) * p * (fw n p s t).1 + (1 - s) * (fw n p s t).2)

lemma avoid_add (n : ℕ) (p s : ℝ) (A : Fin n) (x₀ : Node n) (t : ℕ) :
    ∀ u y, avoid n p s A x₀ (t + u) y =
      ∑ z, avoid n p s A x₀ t z * avoid n p s A z u y := by
  intro u
  induction u with
  | zero =>
    intro y
    simp [avoid]
  | succ u ih =>
    intro y
    rw [← Nat.add_assoc]
    simp only [avoid]
    split_ifs with h
    · simp
    · simp_rw [ih, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun x _ => by ring))

lemma avoid_one (n : ℕ) (p s : ℝ) (A : Fin n) (x₀ z : Node n) :
    avoid n p s A x₀ 1 z = if z = some A then 0 else trans n p s x₀ z := by
  simp [avoid]

lemma survive_succ (n : ℕ) (p s : ℝ) (A : Fin n) (x₀ : Node n) (u : ℕ) :
    survive n p s A x₀ (u + 1) =
      ∑ z, (if z = some A then 0 else trans n p s x₀ z) * survive n p s A z u := by
  unfold survive
  rw [Nat.add_comm]
  simp_rw [avoid_add n p s A x₀ 1 u, avoid_one, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma sum_ne_const (n : ℕ) (A : Fin n) (c : ℝ) :
    ∑ i : Fin n, (if i = A then 0 else c) = ((n : ℝ) - 1) * c := by
  have : ∀ i : Fin n, (if i = A then 0 else c) = c - (if i = A then c else 0) := by
    intro i; split_ifs <;> ring
  simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma survive_eq (n : ℕ) (p s : ℝ) (A : Fin n) :
    ∀ u, survive n p s A none u = (sv n p s u).1 ∧
      ∀ j, j ≠ A → survive n p s A (some j) u = (sv n p s u).2 := by
  intro u
  induction u with
  | zero =>
    refine ⟨?_, fun j _ => ?_⟩ <;> simp [survive, avoid, sv]
  | succ u ih =>
    obtain ⟨ihC, ihE⟩ := ih
    refine ⟨?_, fun j hj => ?_⟩
    · rw [survive_succ, Fintype.sum_option]
      simp only [reduceCtorEq, if_false, UniformPatrol.Star.trans, Option.some.injEq]
      rw [ihC]
      have : ∑ i : Fin n, (if i = A then 0 else p) * survive n p s A (some i) u
          = ∑ i : Fin n, (if i = A then 0 else p * (sv n p s u).2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases hi : i = A
        · simp [hi]
        · simp [hi, ihE i hi]
      rw [this, sum_ne_const]
      simp only [sv]
      ring
    · rw [survive_succ, Fintype.sum_option]
      simp only [reduceCtorEq, if_false, Option.some.injEq]
      simp only [UniformPatrol.Star.trans]
      rw [ihC]
      have : ∑ i : Fin n, (if i = A then 0 else if j = i then 1 - s else 0) *
            survive n p s A (some i) u = (1 - s) * (sv n p s u).2 := by
        rw [Finset.sum_eq_single j]
        · simp [hj, ihE j hj]
        · intro b _ hb
          simp [Ne.symm hb]
        · simp
      rw [this]
      simp only [sv]

lemma fw_eq (n : ℕ) (p s : ℝ) (A : Fin n) :
    ∀ t, avoid n p s A none t none = (fw n p s t).1 ∧
      ∑ i, avoid n p s A none t (some i) = (fw n p s t).2 ∧
      avoid n p s A none t (some A) = 0 := by
  intro t
  induction t with
  | zero => simp [avoid, fw]
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hs : ∀ i, avoid n p s A none (t + 1) (some i) =
        if i = A then 0 else (fw n p s t).1 * p + (1 - s) * avoid n p s A none t (some i) := by
      intro i
      rw [avoid]
      simp only [Option.some.injEq]
      split_ifs with hi
      · rfl
      · rw [Fintype.sum_option]
        simp only [UniformPatrol.Star.trans, Option.some.injEq]
        rw [h1, Finset.sum_eq_single i]
        · simp
          ring
        · intro b _ hb; simp [hb]
        · simp
    refine ⟨?_, ?_, ?_⟩
    · rw [avoid]
      simp only [reduceCtorEq, if_false]
      rw [Fintype.sum_option]
      simp only [UniformPatrol.Star.trans]
      rw [h1, ← Finset.sum_mul, h2]
      simp only [fw]
      ring
    · simp_rw [hs]
      have : ∀ i : Fin n, (if i = A then 0 else (fw n p s t).1 * p +
          (1 - s) * avoid n p s A none t (some i)) =
          (if i = A then 0 else (fw n p s t).1 * p) +
          (1 - s) * avoid n p s A none t (some i) := by
        intro i
        by_cases hi : i = A
        · simp [hi, h3]
        · simp [hi]
      simp_rw [this]
      rw [Finset.sum_add_distrib, sum_ne_const, ← Finset.mul_sum, h2]
      simp only [fw]
      ring
    · rw [hs]; simp

lemma survive_none_add (n : ℕ) (p s : ℝ) (A : Fin n) (t u : ℕ) :
    survive n p s A none (t + u) =
      (fw n p s t).1 * (sv n p s u).1 + (fw n p s t).2 * (sv n p s u).2 := by
  obtain ⟨h1, h2, h3⟩ := fw_eq n p s A t
  obtain ⟨hC, hE⟩ := survive_eq n p s A u
  unfold survive
  simp_rw [avoid_add n p s A none t u]
  rw [Finset.sum_comm, Fintype.sum_option]
  simp_rw [← Finset.mul_sum]
  change avoid n p s A none t none * survive n p s A none u +
    ∑ i, avoid n p s A none t (some i) * survive n p s A (some i) u = _
  rw [h1, hC, ← h2, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : i = A
  · subst hi; simp [h3]
  · rw [hE i hi]

/-- The A-free interception probability. -/
noncomputable def QF (n m : ℕ) (p s : ℝ) (d : ℕ) : ℝ :=
  1 - ((fw n p s (d - 1)).1 * (sv n p s (m - 1)).1 + (fw n p s (d - 1)).2 * (sv n p s (m - 1)).2) /
    ((fw n p s (d - 1)).1 + (fw n p s (d - 1)).2)

lemma Q_eq (n m : ℕ) (hm : 2 ≤ m) (x : PStrat n) (a : AStrat n) :
    Q n m x a = QF n m x.p x.s a.d := by
  have hd := a.one_le_d
  unfold Q QF
  have e1 : a.d + m - 2 = (a.d - 1) + (m - 1) := by omega
  rw [e1, survive_none_add, show a.d - 1 = (a.d - 1) + 0 from rfl, survive_none_add]
  simp [sv]

end UPSol


namespace UPSol
open UniformPatrol.Star

section
variable (n : ℕ) (p s : ℝ)

@[simp] lemma sv_zero : sv n p s 0 = (1, 1) := rfl
@[simp] lemma sv_succ_fst (t : ℕ) : (sv n p s (t + 1)).1 =
    (1 - (n : ℝ) * p) * (sv n p s t).1 + ((n : ℝ) - 1) * p * (sv n p s t).2 := rfl
@[simp] lemma sv_succ_snd (t : ℕ) : (sv n p s (t + 1)).2 =
    s * (sv n p s t).1 + (1 - s) * (sv n p s t).2 := rfl
@[simp] lemma fw_zero : fw n p s 0 = (1, 0) := rfl
@[simp] lemma fw_succ_fst (t : ℕ) : (fw n p s (t + 1)).1 =
    (1 - (n : ℝ) * p) * (fw n p s t).1 + s * (fw n p s t).2 := rfl
@[simp] lemma fw_succ_snd (t : ℕ) : (fw n p s (t + 1)).2 =
    ((n : ℝ) - 1) * p * (fw n p s t).1 + (1 - s) * (fw n p s t).2 := rfl
end

section hyp
variable {n : ℕ} {p s : ℝ} (hn : 2 ≤ n) (hp : 0 < p) (hnp : (n : ℝ) * p ≤ 1)
  (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
include hn hp hnp

lemma w_pos : 0 < ((n : ℝ) - 1) * p := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  positivity

lemma r_nonneg : 0 ≤ 1 - (n : ℝ) * p := by linarith

lemma one_sub_p_pos : 0 < 1 - p := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

include hs0 hs1

lemma sv_mono : ∀ t, (sv n p s (t + 1)).1 ≤ (sv n p s t).1 ∧
    (sv n p s (t + 1)).2 ≤ (sv n p s t).2 ∧ (sv n p s t).1 ≤ (sv n p s (t + 1)).2 := by
  have hw := w_pos hn hp hnp
  have hr := r_nonneg hn hp hnp
  intro t
  induction t with
  | zero =>
    simp only [sv_succ_fst, sv_succ_snd, sv_zero]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [sv_succ_fst, sv_succ_snd] at *
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left h1 hr, mul_le_mul_of_nonneg_left h2 hw.le]
    · nlinarith [mul_le_mul_of_nonneg_left h1 hs0,
        mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hs1)]
    · have : (sv n p s (t + 1)).1 ≤ (sv n p s (t + 1)).2 := le_trans h1 h3
      simp only [sv_succ_fst, sv_succ_snd] at this
      nlinarith [mul_le_mul_of_nonneg_left this (sub_nonneg.mpr hs1)]

lemma sv_C_le_E : ∀ t, (sv n p s t).1 ≤ (sv n p s t).2 := by
  intro t
  cases t with
  | zero => simp
  | succ t =>
    obtain ⟨h1, _, h3⟩ := sv_mono hn hp hnp hs0 hs1 t
    exact le_trans h1 h3

lemma sv_C_anti : Antitone (fun t => (sv n p s t).1) :=
  antitone_nat_of_succ_le (fun t => (sv_mono hn hp hnp hs0 hs1 t).1)

lemma sv_C_strict (hr : 0 < 1 - (n : ℝ) * p) : ∀ t, (sv n p s (t + 1)).1 < (sv n p s t).1 := by
  have hw := w_pos hn hp hnp
  intro t
  induction t with
  | zero => simp; nlinarith
  | succ t ih =>
    obtain ⟨_, h2, _⟩ := sv_mono hn hp hnp hs0 hs1 t
    have e : (sv n p s (t + 1 + 1)).1 = (1 - (n : ℝ) * p) * (sv n p s (t + 1)).1 +
        ((n : ℝ) - 1) * p * (sv n p s (t + 1)).2 := rfl
    have e2 : (sv n p s (t + 1)).1 = (1 - (n : ℝ) * p) * (sv n p s t).1 +
        ((n : ℝ) - 1) * p * (sv n p s t).2 := rfl
    rw [e, e2]
    rw [e2] at ih
    nlinarith [mul_lt_mul_of_pos_left ih hr, mul_le_mul_of_nonneg_left h2 hw.le]

lemma sv_C_lt_E (hr : 0 < 1 - (n : ℝ) * p) (t : ℕ) (ht : 1 ≤ t) :
    (sv n p s t).1 < (sv n p s t).2 := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  exact lt_of_lt_of_le (sv_C_strict hn hp hnp hs0 hs1 hr k) (sv_mono hn hp hnp hs0 hs1 k).2.2

lemma fw_nonneg : ∀ t, 0 ≤ (fw n p s t).1 ∧ 0 ≤ (fw n p s t).2 ∧
    0 < (fw n p s t).1 + (fw n p s t).2 := by
  have hw := w_pos hn hp hnp
  have hr := r_nonneg hn hp hnp
  have hq := one_sub_p_pos hn hp hnp
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [fw_succ_fst, fw_succ_snd]
    refine ⟨by positivity, ?_, ?_⟩
    · have : 0 ≤ 1 - s := sub_nonneg.mpr hs1
      positivity
    · nlinarith

/-- conditional-centre comparison: if `s (1-p) ≥ r` then every delay has centre weight
at least that of delay two. -/
lemma fw_kappa (hk : 1 - (n : ℝ) * p ≤ s * (1 - p)) : ∀ t,
    (1 - (n : ℝ) * p) * ((fw n p s t).1 + (fw n p s t).2) ≤ (fw n p s t).1 * (1 - p) := by
  have hw := w_pos hn hp hnp
  intro t
  cases t with
  | zero => simp; nlinarith
  | succ t =>
    obtain ⟨_, h2, _⟩ := fw_nonneg hn hp hnp hs0 hs1 t
    simp only [fw_succ_fst, fw_succ_snd]
    nlinarith [mul_le_mul_of_nonneg_left hk h2]

lemma fw_pos_one (hr : 0 < 1 - (n : ℝ) * p) : ∀ t, 0 < (fw n p s t).1 := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨_, h2, _⟩ := fw_nonneg hn hp hnp hs0 hs1 t
    simp only [fw_succ_fst]
    have : 0 ≤ s * (fw n p s t).2 := mul_nonneg hs0 h2
    nlinarith [mul_pos hr ih]

end hyp

/-- real comparison lemma -/
lemma cmp_le (α β α' β' C E : ℝ) (hab : 0 < α + β) (hab' : 0 < α' + β') (hCE : C ≤ E)
    (hk : α' * (α + β) ≤ α * (α' + β')) :
    1 - (α' * C + β' * E) / (α' + β') ≤ 1 - (α * C + β * E) / (α + β) := by
  rw [sub_le_sub_iff_left, div_le_div_iff₀ hab hab']
  nlinarith [mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hCE)]

lemma cmp_lt (α β α' β' C E : ℝ) (hab : 0 < α + β) (hab' : 0 < α' + β') (hCE : C < E)
    (hk : α' * (α + β) < α * (α' + β')) :
    1 - (α' * C + β' * E) / (α' + β') < 1 - (α * C + β * E) / (α + β) := by
  rw [sub_lt_sub_iff_left, div_lt_div_iff₀ hab hab']
  nlinarith [mul_lt_mul_of_pos_right hk (sub_pos.mpr hCE)]

lemma QF_two {n m : ℕ} (hm : 1 ≤ m) (p s : ℝ) :
    QF n m p s 2 = 1 - (sv n p s m).1 / (1 - p) := by
  unfold QF
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [show 2 - 1 = 0 + 1 from rfl, fw_succ_fst, fw_succ_snd, fw_zero,
    Nat.add_sub_cancel, sv_succ_fst]
  congr 2 <;> ring

/-- Lemma 3 (comparison of delays) in A-free form. -/
lemma QF_delay_le {n m : ℕ} (hn : 2 ≤ n) {p s : ℝ} (hp : 0 < p) (hnp : (n : ℝ) * p ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hk : 1 - (n : ℝ) * p ≤ s * (1 - p)) (d : ℕ) :
    QF n m p s 2 ≤ QF n m p s d := by
  unfold QF
  obtain ⟨_, _, h3⟩ := fw_nonneg hn hp hnp hs0 hs1 (d - 1)
  obtain ⟨_, _, h3'⟩ := fw_nonneg hn hp hnp hs0 hs1 (2 - 1)
  apply cmp_le _ _ _ _ _ _ h3 h3' (sv_C_le_E hn hp hnp hs0 hs1 _)
  have := fw_kappa hn hp hnp hs0 hs1 hk (d - 1)
  simp only [show 2 - 1 = 0 + 1 from rfl, fw_succ_fst, fw_succ_snd, fw_zero]
  nlinarith

lemma QF_delay_lt {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) {p : ℝ} (hp : 0 < p)
    (hnp : (n : ℝ) * p < 1) (d : ℕ) (hd1 : 1 ≤ d) (hd : d ≠ 2) :
    QF n m p 1 2 < QF n m p 1 d := by
  have hnp' := hnp.le
  have hr : 0 < 1 - (n : ℝ) * p := by linarith
  have hw := w_pos hn hp hnp'
  unfold QF
  obtain ⟨_, _, h3⟩ := fw_nonneg hn hp hnp' zero_le_one le_rfl (d - 1)
  obtain ⟨_, _, h3'⟩ := fw_nonneg hn hp hnp' zero_le_one le_rfl (2 - 1)
  apply cmp_lt _ _ _ _ _ _ h3 h3' (sv_C_lt_E hn hp hnp' zero_le_one le_rfl hr _ (by omega))
  simp only [show 2 - 1 = 0 + 1 from rfl, fw_succ_fst, fw_succ_snd, fw_zero]
  rcases Nat.lt_or_ge d 2 with h | h
  · have : d = 1 := by omega
    subst this
    simp
    nlinarith
  · obtain ⟨k, hk⟩ : ∃ k, d - 1 = k + 1 + 1 := ⟨d - 3, by omega⟩
    rw [hk]
    have ha := fw_pos_one hn hp hnp' zero_le_one le_rfl hr k
    have hb := (fw_nonneg hn hp hnp' zero_le_one le_rfl k).2.1
    simp only [fw_succ_fst, fw_succ_snd]
    simp only [sub_self, zero_mul, add_zero, one_mul]
    nlinarith [mul_pos hw ha, mul_pos (mul_pos hw ha) hw]

/-- Lemma 1 core: reflection dominates. -/
lemma sv_refl_le {n : ℕ} (hn : 2 ≤ n) {p s : ℝ} (hp : 0 < p) (hnp : (n : ℝ) * p ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : ∀ t,
    (sv n p 1 t).1 ≤ (sv n p s t).1 ∧ (sv n p 1 t).2 ≤ (sv n p s t).2 := by
  have hw := w_pos hn hp hnp
  have hr := r_nonneg hn hp hnp
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    have hCE := sv_C_le_E hn hp hnp zero_le_one le_rfl t
    simp only [sv_succ_fst, sv_succ_snd]
    refine ⟨?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left h1 hr, mul_le_mul_of_nonneg_left h2 hw.le]
    · nlinarith [mul_le_mul_of_nonneg_left h1 hs0,
        mul_le_mul_of_nonneg_left (le_trans hCE h2) (sub_nonneg.mpr hs1)]

lemma sv_refl_lt {n : ℕ} (hn : 2 ≤ n) {p s : ℝ} (hp : 0 < p) (hnp : (n : ℝ) * p ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) : ∀ t, 2 ≤ t → (sv n p 1 t).2 < (sv n p s t).2 := by
  have hw := w_pos hn hp hnp
  have h1s : 0 < 1 - s := by linarith
  intro t ht
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
  clear ht
  induction k with
  | zero =>
    obtain ⟨h1, h2⟩ := sv_refl_le hn hp hnp hs0 hs1.le 1
    simp only [sv_succ_fst, sv_succ_snd, sv_zero] at *
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := sv_refl_le hn hp hnp hs0 hs1.le (k + 2)
    have hCE := sv_C_le_E hn hp hnp zero_le_one le_rfl (k + 2)
    have e1 : (sv n p 1 (k + 1 + 2)).2 = (sv n p 1 (k + 2)).1 := by
      show 1 * _ + (1 - 1) * _ = _; ring
    have e2 : (sv n p s (k + 1 + 2)).2 = s * (sv n p s (k + 2)).1 + (1 - s) * (sv n p s (k + 2)).2 := rfl
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0, mul_lt_mul_of_pos_left ih h1s,
      mul_le_mul_of_nonneg_left hCE h1s.le]

lemma QF_refl_le {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) {p s : ℝ} (hp : 0 < p)
    (hnp : (n : ℝ) * p ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    QF n m p s 2 ≤ QF n m p 1 2 := by
  rw [QF_two (by omega), QF_two (by omega)]
  have hq := one_sub_p_pos hn hp hnp
  have := (sv_refl_le hn hp hnp hs0 hs1 m).1
  rw [sub_le_sub_iff_left]
  exact div_le_div_of_nonneg_right this hq.le

lemma QF_refl_lt {n m : ℕ} (hn : 2 ≤ n) (hm : 3 ≤ m) {p s : ℝ} (hp : 0 < p)
    (hnp : (n : ℝ) * p ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    QF n m p s 2 < QF n m p 1 2 := by
  rw [QF_two (by omega), QF_two (by omega)]
  have hq := one_sub_p_pos hn hp hnp
  have hw := w_pos hn hp hnp
  have hr := r_nonneg hn hp hnp
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 := (sv_refl_le hn hp hnp hs0 hs1.le k).1
  have h2 := sv_refl_lt hn hp hnp hs0 hs1 k (by omega)
  have : (sv n p 1 (k + 1)).1 < (sv n p s (k + 1)).1 := by
    simp only [sv_succ_fst]
    nlinarith [mul_le_mul_of_nonneg_left h1 hr, mul_lt_mul_of_pos_left h2 hw]
  rw [sub_lt_sub_iff_left]
  exact div_lt_div_of_pos_right this hq

end UPSol


namespace UPSol
open UniformPatrol.Star

lemma q_facts {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ ((n : ℝ) - 1) / n ∧ ((n : ℝ) - 1) / n ≤ 1 ∧ ((n : ℝ) - 1) / n * n = n - 1 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨div_nonneg (by linarith) hn0.le, (div_le_one hn0).mpr (by linarith), ?_⟩
  field_simp

/-- Lower bounds behind Proposition 2. -/
lemma sv_lower {n : ℕ} (hn : 2 ≤ n) {p s : ℝ} (hp : 0 < p) (hnp : (n : ℝ) * p ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : ∀ i,
    (((n : ℝ) - 1) / n) ^ i ≤ (sv n p s (2 * i)).1 ∧
    (((n : ℝ) - 1) / n) ^ (i + 1) ≤ (sv n p s (2 * i + 1)).1 ∧
    (((n : ℝ) - 1) / n) ^ i ≤ (sv n p s (2 * i)).2 ∧
    (((n : ℝ) - 1) / n) ^ i ≤ (sv n p s (2 * i + 1)).2 := by
  obtain ⟨hq0, hq1, hqn⟩ := q_facts hn
  set q := ((n : ℝ) - 1) / n with hq
  have hw := w_pos hn hp hnp
  have hr := r_nonneg hn hp hnp
  have key : (1 - (n : ℝ) * p) * q + ((n : ℝ) - 1) * p = q := by
    have : (n : ℝ) * p * q = ((n : ℝ) - 1) * p := by rw [← hqn]; ring
    linarith
  have hpq : q ≤ 1 - p := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have : q * n ≤ (1 - p) * n := by rw [hqn]; nlinarith
    exact le_of_mul_le_mul_right this (by linarith)
  have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  intro i
  induction i with
  | zero =>
    simp only [pow_zero, zero_add, pow_one, Nat.mul_zero, sv_zero, sv_succ_fst, sv_succ_snd]
    refine ⟨le_rfl, by nlinarith, le_rfl, by nlinarith⟩
  | succ i ih =>
    obtain ⟨a1, a2, a3, a4⟩ := ih
    set X := q ^ i with hX
    have hX0 : 0 ≤ X := pow_nonneg hq0 i
    have e1 : q ^ (i + 1) = q * X := by rw [pow_succ]; ring
    have e2 : q ^ (i + 1 + 1) = q * (q * X) := by rw [pow_succ, pow_succ]; ring
    rw [e1] at a2 ⊢
    rw [e2]
    have i1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    have i2 : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by ring
    rw [i1]
    have qX : q * X ≤ X := by nlinarith
    -- values at 2i+2
    have c2 : q * X ≤ (sv n p s (2 * i + 1 + 1)).1 := by
      have ee : (sv n p s (2 * i + 1 + 1)).1 = (1 - (n : ℝ) * p) * (sv n p s (2 * i + 1)).1 +
          ((n : ℝ) - 1) * p * (sv n p s (2 * i + 1)).2 := rfl
      rw [ee]
      have := mul_le_mul_of_nonneg_left a2 hr
      have := mul_le_mul_of_nonneg_left a4 hw.le
      have : q * X = (1 - (n : ℝ) * p) * (q * X) + ((n : ℝ) - 1) * p * X := by
        linear_combination (-X) * key
      linarith
    have e2' : q * X ≤ (sv n p s (2 * i + 1 + 1)).2 := by
      have ee : (sv n p s (2 * i + 1 + 1)).2 = s * (sv n p s (2 * i + 1)).1 +
          (1 - s) * (sv n p s (2 * i + 1)).2 := rfl
      rw [ee]
      nlinarith [mul_le_mul_of_nonneg_left a2 hs0, mul_le_mul_of_nonneg_left (le_trans qX a4) h1s]
    refine ⟨c2, ?_, e2', ?_⟩
    · have : (sv n p s (2 * i + 1 + 1 + 1)).1 = (1 - (n : ℝ) * p) * (sv n p s (2 * i + 1 + 1)).1 +
          ((n : ℝ) - 1) * p * (sv n p s (2 * i + 1 + 1)).2 := rfl
      rw [this]
      have := mul_le_mul_of_nonneg_left c2 hr
      have := mul_le_mul_of_nonneg_left e2' hw.le
      have : q * (q * X) ≤ (1 - p) * (q * X) := mul_le_mul_of_nonneg_right hpq (by positivity)
      nlinarith
    · have : (sv n p s (2 * i + 1 + 1 + 1)).2 = s * (sv n p s (2 * i + 1 + 1)).1 +
          (1 - s) * (sv n p s (2 * i + 1 + 1)).2 := rfl
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left c2 hs0, mul_le_mul_of_nonneg_left e2' h1s]

/-- Exact values for the zero-holding reflecting walk. -/
lemma sv_exact {n : ℕ} (hn : 2 ≤ n) : ∀ i,
    (sv n (1 / n) 1 (2 * i)).1 = (((n : ℝ) - 1) / n) ^ i ∧
    (sv n (1 / n) 1 (2 * i + 1)).1 = (((n : ℝ) - 1) / n) ^ (i + 1) ∧
    (sv n (1 / n) 1 (2 * i)).2 = (((n : ℝ) - 1) / n) ^ i ∧
    (sv n (1 / n) 1 (2 * i + 1)).2 = (((n : ℝ) - 1) / n) ^ i := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have r0 : 1 - (n : ℝ) * (1 / n) = 0 := by field_simp; ring
  have w0 : ((n : ℝ) - 1) * (1 / n) = ((n : ℝ) - 1) / n := by ring
  intro i
  induction i with
  | zero =>
    simp only [pow_zero, zero_add, pow_one, Nat.mul_zero, sv_zero, sv_succ_fst, sv_succ_snd, r0, w0]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | ring
  | succ i ih =>
    obtain ⟨a1, a2, a3, a4⟩ := ih
    have i1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    have i2 : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by ring
    rw [i1]
    simp only [sv_succ_fst, sv_succ_snd, r0, w0] at *
    simp only [a2, a4, a1, a3] at *
    refine ⟨by ring, by ring, by ring, by ring⟩

lemma QF_odd_le {n m : ℕ} (hn : 2 ≤ n) (j : ℕ) (hmj : m = 2 * j + 1) {p s : ℝ} (hp : 0 < p)
    (hnp : (n : ℝ) * p ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (d : ℕ) :
    QF n m p s d ≤ 1 - (((n : ℝ) - 1) / n) ^ j := by
  unfold QF
  rw [hmj, Nat.add_sub_cancel]
  obtain ⟨h1, _, h3, _⟩ := sv_lower hn hp hnp hs0 hs1 j
  obtain ⟨g1, g2, g3⟩ := fw_nonneg hn hp hnp hs0 hs1 (d - 1)
  rw [sub_le_sub_iff_left, le_div_iff₀ g3]
  nlinarith [mul_le_mul_of_nonneg_left h1 g1, mul_le_mul_of_nonneg_left h3 g2]

lemma QF_odd_eq {n m : ℕ} (hn : 2 ≤ n) (j : ℕ) (hmj : m = 2 * j + 1) (d : ℕ) :
    QF n m (1 / n) 1 d = 1 - (((n : ℝ) - 1) / n) ^ j := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < 1 / n := by positivity
  have hnp : (n : ℝ) * (1 / n) ≤ 1 := by field_simp; rfl
  unfold QF
  rw [hmj, Nat.add_sub_cancel]
  obtain ⟨h1, _, h3, _⟩ := sv_exact hn j
  obtain ⟨g1, g2, g3⟩ := fw_nonneg hn hp hnp zero_le_one le_rfl (d - 1)
  rw [h1, h3]
  congr 1
  field_simp

lemma sv_p0 (n : ℕ) (s : ℝ) : ∀ t, sv n 0 s t = (1, 1) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    ext
    · simp only [sv_succ_fst, ih]; ring
    · simp only [sv_succ_snd, ih]; ring

lemma sv_cont (n : ℕ) : ∀ t, Continuous (fun p => (sv n p 1 t).1) ∧
    Continuous (fun p => (sv n p 1 t).2) := by
  intro t
  induction t with
  | zero => simp only [sv_zero]; exact ⟨continuous_const, continuous_const⟩
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · show Continuous (fun p => (1 - (n : ℝ) * p) * (sv n p 1 t).1 + ((n : ℝ) - 1) * p * (sv n p 1 t).2)
      fun_prop
    · show Continuous (fun p => (1 : ℝ) * (sv n p 1 t).1 + (1 - 1) * (sv n p 1 t).2)
      fun_prop

/-- Derivatives (in p) of the reflecting survival pair. -/
def dsv (n : ℕ) (p : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | t + 1 => (-(n : ℝ) * (sv n p 1 t).1 + (1 - (n : ℝ) * p) * (dsv n p t).1 +
      (((n : ℝ) - 1) * (sv n p 1 t).2 + ((n : ℝ) - 1) * p * (dsv n p t).2), (dsv n p t).1)

lemma sv_deriv (n : ℕ) (p0 : ℝ) : ∀ t,
    HasDerivAt (fun p => (sv n p 1 t).1) (dsv n p0 t).1 p0 ∧
    HasDerivAt (fun p => (sv n p 1 t).2) (dsv n p0 t).2 p0 := by
  intro t
  induction t with
  | zero =>
    simp only [sv_zero]
    exact ⟨hasDerivAt_const _ _, hasDerivAt_const _ _⟩
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    have ha : HasDerivAt (fun p : ℝ => 1 - (n : ℝ) * p) (-(n : ℝ)) p0 := by
      simpa using ((hasDerivAt_id p0).const_mul (n : ℝ)).const_sub 1
    have hb : HasDerivAt (fun p : ℝ => ((n : ℝ) - 1) * p) ((n : ℝ) - 1) p0 := by
      simpa using (hasDerivAt_id p0).const_mul ((n : ℝ) - 1)
    refine ⟨?_, ?_⟩
    · have := (ha.mul h1).add (hb.mul h2)
      exact this
    · have := ((hasDerivAt_const p0 (1 : ℝ)).mul h1).add ((hasDerivAt_const p0 ((1 : ℝ) - 1)).mul h2)
      have e : (0 : ℝ) * (sv n p0 1 t).1 + 1 * (dsv n p0 t).1 +
          ((0 : ℝ) * (sv n p0 1 t).2 + (1 - 1) * (dsv n p0 t).2) = (dsv n p0 (t + 1)).2 := by
        show _ = (dsv n p0 t).1
        ring
      rw [e] at this
      exact this

lemma dsv_even_zero {n : ℕ} (hn : 2 ≤ n) : ∀ i, (dsv n (1 / n) (2 * i)).1 = 0 := by
  obtain ⟨_, _, hqn⟩ := q_facts hn
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have r0 : 1 - (n : ℝ) * (1 / n) = 0 := by field_simp; ring
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    obtain ⟨_, a2, _, a4⟩ := sv_exact hn i
    have i1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    rw [i1]
    show -(n : ℝ) * (sv n (1 / n) 1 (2 * i + 1)).1 + (1 - (n : ℝ) * (1 / n)) * (dsv n (1 / n) (2 * i + 1)).1 +
      (((n : ℝ) - 1) * (sv n (1 / n) 1 (2 * i + 1)).2 + ((n : ℝ) - 1) * (1 / n) * (dsv n (1 / n) (2 * i)).1) = 0
    rw [a2, a4, r0, ih, pow_succ]
    have : ((n : ℝ) - 1) / n * n = n - 1 := hqn
    linear_combination (-(((n : ℝ) - 1) / n) ^ i) * this

/-- For even durations the value at p = 1/n is beaten by some smaller p. -/
lemma even_beat {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / n ∧
      (sv n p 1 (2 * k)).1 < (((n : ℝ) - 1) / n) ^ (k - 1) * (1 - p) := by
  obtain ⟨hq0, hq1, hqn⟩ := q_facts hn
  set q := ((n : ℝ) - 1) / n with hq
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hq0' : 0 < q := by rw [hq]; apply div_pos <;> linarith
  set p0 : ℝ := 1 / n with hp0
  have hp0pos : 0 < p0 := by positivity
  let G : ℝ → ℝ := fun p => (sv n p 1 (2 * k)).1 - q ^ (k - 1) * (1 - p)
  have hG : HasDerivAt G (0 + q ^ (k - 1)) p0 := by
    have h1 := (sv_deriv n p0 (2 * k)).1
    rw [dsv_even_zero hn k] at h1
    have h3 : HasDerivAt (fun p : ℝ => q ^ (k - 1) * (1 - p)) (-(q ^ (k - 1))) p0 := by
      simpa using ((hasDerivAt_id p0).const_sub 1).const_mul (q ^ (k - 1))
    have h4 : HasDerivAt (fun p => (sv n p 1 (2 * k)).1 - q ^ (k - 1) * (1 - p))
        (0 - -(q ^ (k - 1))) p0 := h1.sub h3
    convert h4 using 1
    ring
  have hG0 : G p0 = 0 := by
    show (sv n p0 1 (2 * k)).1 - q ^ (k - 1) * (1 - p0) = 0
    rw [(sv_exact hn k).1]
    have : 1 - p0 = q := by rw [hp0, hq]; field_simp
    rw [this, ← pow_succ, Nat.sub_add_cancel hk]
    ring
  have hpos : 0 < 0 + q ^ (k - 1) := by simp; positivity
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hG)
  have hsl' := hsl.mono_left (nhdsWithin_mono p0 (fun x hx => ne_of_lt hx : Set.Iio p0 ⊆ {p0}ᶜ))
  have ev1 : ∀ᶠ p in nhdsWithin p0 (Set.Iio p0), 0 < slope G p0 p :=
    hsl'.eventually (lt_mem_nhds hpos)
  have ev2 : ∀ᶠ p in nhdsWithin p0 (Set.Iio p0), p ∈ Set.Ioo 0 p0 :=
    Ioo_mem_nhdsLT hp0pos
  obtain ⟨p, hsp, hpI⟩ := (ev1.and ev2).exists
  refine ⟨p, hpI.1, hpI.2, ?_⟩
  rw [slope_def_field, hG0] at hsp
  have hd : p - p0 < 0 := by linarith [hpI.2]
  have : G p - 0 < 0 := by
    by_contra hc
    push_neg at hc
    have := div_nonpos_of_nonneg_of_nonpos hc hd.le
    linarith
  have hGp : (sv n p 1 (2 * k)).1 - q ^ (k - 1) * (1 - p) < 0 := by
    have h' : G p < 0 := by linarith
    exact h'
  linarith

end UPSol


namespace UPSol
open UniformPatrol.Star

lemma F_pos {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) {p : ℝ} (hp : 0 < p) (hnp : (n : ℝ) * p < 1) :
    0 < 1 - (sv n p 1 m).1 / (1 - p) := by
  have hq := one_sub_p_pos hn hp hnp.le
  have hw := w_pos hn hp hnp.le
  have h2 : (sv n p 1 m).1 ≤ (sv n p 1 2).1 := sv_C_anti hn hp hnp.le zero_le_one le_rfl hm
  have e : (sv n p 1 2).1 = (1 - (n : ℝ) * p) * (1 - p) + ((n : ℝ) - 1) * p := by
    show (1 - (n : ℝ) * p) * ((1 - (n : ℝ) * p) * 1 + ((n : ℝ) - 1) * p * 1) +
      ((n : ℝ) - 1) * p * (1 * 1 + (1 - 1) * 1) = _
    ring
  have : (sv n p 1 2).1 < 1 - p := by
    rw [e]; nlinarith
  rw [sub_pos, div_lt_one hq]
  linarith

lemma exists_max {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    ∃ ps : ℝ, 0 < ps ∧ (n : ℝ) * ps ≤ 1 ∧
      (∀ p : ℝ, 0 < p → (n : ℝ) * p ≤ 1 → QF n m p 1 2 ≤ QF n m ps 1 2) ∧
      (Even m → (n : ℝ) * ps < 1) := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let F : ℝ → ℝ := fun p => 1 - (sv n p 1 m).1 / (1 - p)
  have hFQ : ∀ p, QF n m p 1 2 = F p := fun p => QF_two (by omega) p 1
  have hcont : ContinuousOn F (Set.Icc 0 (1 / n)) := by
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div (sv_cont n m).1.continuousOn (by fun_prop)
    intro p hp
    have : p ≤ 1 / n := hp.2
    have : 1 / (n : ℝ) < 1 := by rw [div_lt_one hn0]; linarith
    linarith
  obtain ⟨ps, hpsI, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 1 / n)) hcont
  have hle : ∀ p ∈ Set.Icc (0 : ℝ) (1 / n), F p ≤ F ps := fun p hp => hmax hp
  have hF0 : F 0 = 0 := by
    show 1 - (sv n 0 1 m).1 / (1 - 0) = 0
    rw [sv_p0]; simp
  have hp1 : (0 : ℝ) < 1 / (2 * n) := by positivity
  have hp1n : (n : ℝ) * (1 / (2 * n)) < 1 := by
    rw [show (n : ℝ) * (1 / (2 * n)) = 1 / 2 by field_simp]; norm_num
  have hFp1 : 0 < F (1 / (2 * n)) := F_pos hn hm hp1 hp1n
  have hp1I : 1 / (2 * (n : ℝ)) ∈ Set.Icc (0 : ℝ) (1 / n) := by
    refine ⟨hp1.le, ?_⟩
    apply div_le_div_of_nonneg_left zero_le_one hn0 (by linarith)
  have hps_pos : 0 < ps := by
    rcases lt_or_eq_of_le hpsI.1 with h | h
    · exact h
    · exfalso
      have := hle _ hp1I
      rw [← h, hF0] at this
      linarith
  have hnps : (n : ℝ) * ps ≤ 1 := by
    have := hpsI.2
    calc (n : ℝ) * ps ≤ n * (1 / n) := by gcongr
      _ = 1 := by field_simp
  refine ⟨ps, hps_pos, hnps, ?_, ?_⟩
  · intro p hp hnp
    rw [hFQ, hFQ]
    apply hle
    refine ⟨hp.le, ?_⟩
    rw [le_div_iff₀ hn0]; linarith
  · rintro ⟨k, hk⟩
    have hk1 : 1 ≤ k := by omega
    obtain ⟨p, hp, hpn, hlt⟩ := even_beat hn k hk1
    rcases lt_or_eq_of_le hnps with h | h
    · exact h
    · exfalso
      have hps : ps = 1 / n := by field_simp; linarith
      have hmk : m = 2 * k := by omega
      have hpI : p ∈ Set.Icc (0 : ℝ) (1 / n) := ⟨hp.le, hpn.le⟩
      have h1 := hle p hpI
      -- F ps = 1 - q^(k-1)
      have hFps : F ps = 1 - (((n : ℝ) - 1) / n) ^ (k - 1) := by
        show 1 - (sv n ps 1 m).1 / (1 - ps) = _
        rw [hps, hmk, (sv_exact hn k).1]
        have : 1 - 1 / (n : ℝ) = ((n : ℝ) - 1) / n := by field_simp
        rw [this]
        congr 1
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hq : ((n : ℝ) - 1) / n ≠ 0 := by
          apply div_ne_zero _ hn0.ne'; linarith
        rw [Nat.add_sub_cancel, pow_succ, mul_div_assoc, div_self hq, mul_one]
      have hpn' := (lt_div_iff₀ hn0).mp hpn
      have hq1 := one_sub_p_pos hn hp (by linarith : (n : ℝ) * p ≤ 1)
      have hFp : F p = 1 - (sv n p 1 m).1 / (1 - p) := rfl
      rw [hFps, hFp, hmk] at h1
      have : (sv n p 1 (2 * k)).1 / (1 - p) < (((n : ℝ) - 1) / n) ^ (k - 1) := by
        rw [div_lt_iff₀ hq1]; exact hlt
      linarith

end UPSol

open UniformPatrol.Star UPSol in
theorem UPSol.thm1_main (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∃ x : PStrat n, x.s = 1 ∧
      ∀ a : AStrat n, a.d = 2 → IsSaddle n m x a) ∧
    ((∀ a : AStrat n, IsOptimalA n m a → a.d = 2) ↔ Even m) ∧
    ((∀ x : PStrat n, IsOptimalP n m x → x.s = 1) ↔ 3 ≤ m) := by
  obtain ⟨ps, hps, hnps, hmax, heven⟩ := exists_max hn hm
  let xs : PStrat n := ⟨ps, 1, hps, hnps, one_pos, le_rfl⟩
  have saddle : ∀ a : AStrat n, a.d = 2 → IsSaddle n m xs a := by
    intro a ha
    refine ⟨fun x' => ?_, fun a' => ?_⟩
    · rw [Q_eq n m hm, Q_eq n m hm, ha]
      exact le_trans (QF_refl_le hn hm x'.p_pos x'.np_le x'.s_pos.le x'.s_le)
        (hmax x'.p x'.p_pos x'.np_le)
    · rw [Q_eq n m hm, Q_eq n m hm, ha]
      have hk : 1 - (n : ℝ) * ps ≤ 1 * (1 - ps) := by
        have := w_pos hn hps hnps; nlinarith
      exact QF_delay_le hn hps hnps zero_le_one le_rfl hk a'.d
  have hA0 : 0 < n := by omega
  refine ⟨⟨xs, rfl, saddle⟩, ?_, ?_⟩
  · constructor
    · intro h
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      obtain ⟨j, hj⟩ := hodd
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      let x1 : PStrat n := ⟨1 / n, 1, by positivity, by field_simp; rfl, one_pos, le_rfl⟩
      let a0 : AStrat n := ⟨⟨0, hA0⟩, 1, le_rfl⟩
      have hopt : IsOptimalA n m a0 := by
        refine ⟨x1, fun x' => ?_, fun a' => ?_⟩
        · rw [Q_eq n m hm, Q_eq n m hm]
          rw [QF_odd_eq hn j hj]
          exact QF_odd_le hn j hj x'.p_pos x'.np_le x'.s_pos.le x'.s_le _
        · rw [Q_eq n m hm, Q_eq n m hm]
          show QF n m (1 / n) 1 1 ≤ QF n m (1 / n) 1 a'.d
          rw [QF_odd_eq hn j hj, QF_odd_eq hn j hj]
      have := h a0 hopt
      simp [a0] at this
    · intro he a ⟨x, hx⟩
      by_contra hd
      have hnps' := heven he
      let as : AStrat n := ⟨a.A, 2, by norm_num⟩
      have hs := saddle as rfl
      have c1 : Q n m xs a ≤ Q n m x a := hx.1 xs
      have c2 : Q n m x a ≤ Q n m x as := hx.2 as
      have c3 : Q n m x as ≤ Q n m xs as := hs.1 x
      have c4 : Q n m xs as < Q n m xs a := by
        rw [Q_eq n m hm, Q_eq n m hm]
        exact QF_delay_lt hn hm hps hnps' a.d a.one_le_d hd
      linarith
  · constructor
    · intro h
      by_contra hlt
      have hm2 : m = 2 := by omega
      have hnps' : (n : ℝ) * ps < 1 := heven ⟨1, by omega⟩
      have hq := one_sub_p_pos hn hps hnps
      have hw := w_pos hn hps hnps
      set s0 := (1 - (n : ℝ) * ps) / (1 - ps) with hs0
      have hs0pos : 0 < s0 := div_pos (by linarith) hq
      have hs0lt : s0 < 1 := by rw [hs0, div_lt_one hq]; nlinarith
      let y : PStrat n := ⟨ps, s0, hps, hnps, hs0pos, hs0lt.le⟩
      let as : AStrat n := ⟨⟨0, hA0⟩, 2, by norm_num⟩
      have hQy : QF n m ps s0 2 = QF n m ps 1 2 := by
        rw [QF_two (by omega), QF_two (by omega), hm2]
        congr 2
        show (1 - (n : ℝ) * ps) * ((1 - (n : ℝ) * ps) * 1 + ((n : ℝ) - 1) * ps * 1) +
            ((n : ℝ) - 1) * ps * (s0 * 1 + (1 - s0) * 1) =
          (1 - (n : ℝ) * ps) * ((1 - (n : ℝ) * ps) * 1 + ((n : ℝ) - 1) * ps * 1) +
            ((n : ℝ) - 1) * ps * (1 * 1 + (1 - 1) * 1)
        ring
      have hopt : IsOptimalP n m y := by
        refine ⟨as, fun x' => ?_, fun a' => ?_⟩
        · rw [Q_eq n m hm, Q_eq n m hm]
          show QF n m x'.p x'.s 2 ≤ QF n m ps s0 2
          rw [hQy]
          exact le_trans (QF_refl_le hn hm x'.p_pos x'.np_le x'.s_pos.le x'.s_le)
            (hmax x'.p x'.p_pos x'.np_le)
        · rw [Q_eq n m hm, Q_eq n m hm]
          have hk : 1 - (n : ℝ) * ps ≤ s0 * (1 - ps) := by
            rw [hs0, div_mul_cancel₀ _ hq.ne']
          exact QF_delay_le hn hps hnps hs0pos.le hs0lt.le hk a'.d
      have := h y hopt
      have : s0 = 1 := this
      linarith
    · intro h3 x ⟨a, hx⟩
      by_contra hs
      have hs' : x.s < 1 := lt_of_le_of_ne x.s_le hs
      let as : AStrat n := ⟨a.A, 2, by norm_num⟩
      have hsd := saddle as rfl
      have c1 : Q n m xs as ≤ Q n m xs a := hsd.2 a
      have c2 : Q n m xs a ≤ Q n m x a := hx.1 xs
      have c3 : Q n m x a ≤ Q n m x as := hx.2 as
      have c4 : Q n m x as < Q n m xs as := by
        rw [Q_eq n m hm, Q_eq n m hm]
        exact lt_of_lt_of_le (QF_refl_lt hn h3 x.p_pos x.np_le x.s_pos.le hs')
          (hmax x.p x.p_pos x.np_le)
      linarith



namespace UPSol
open UniformPatrol.Star

lemma QF_m2_indep (n : ℕ) (p s : ℝ) : QF n 2 p s 2 = QF n 2 p 1 2 := by
  rw [QF_two (by norm_num), QF_two (by norm_num)]
  congr 2
  show (1 - (n : ℝ) * p) * ((1 - (n : ℝ) * p) * 1 + ((n : ℝ) - 1) * p * 1) +
      ((n : ℝ) - 1) * p * (s * 1 + (1 - s) * 1) =
    (1 - (n : ℝ) * p) * ((1 - (n : ℝ) * p) * 1 + ((n : ℝ) - 1) * p * 1) +
      ((n : ℝ) - 1) * p * (1 * 1 + (1 - 1) * 1)
  ring

lemma sv_C_lt_E_s {n : ℕ} (hn : 2 ≤ n) {p s : ℝ} (hp : 0 < p) (hnp : (n : ℝ) * p ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) : ∀ u, 1 ≤ u → (sv n p s u).1 < (sv n p s u).2 := by
  intro u hu
  obtain ⟨k, rfl⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
  clear hu
  induction k with
  | zero =>
    show (1 - (n : ℝ) * p) * 1 + ((n : ℝ) - 1) * p * 1 < s * 1 + (1 - s) * 1
    nlinarith
  | succ k ih =>
    have hanti := (sv_mono hn hp hnp hs0 hs1.le (k + 1)).1
    have e : (sv n p s (k + 1 + 1)).2 = s * (sv n p s (k + 1)).1 + (1 - s) * (sv n p s (k + 1)).2 := rfl
    rw [e]
    have : 0 < 1 - s := by linarith
    nlinarith [mul_lt_mul_of_pos_left ih this]

lemma survive_none_eq {n : ℕ} (p s : ℝ) (A : Fin n) (t : ℕ) :
    survive n p s A none t = (fw n p s t).1 + (fw n p s t).2 := by
  have := survive_none_add n p s A t 0
  simp only [Nat.add_zero, sv_zero, mul_one] at this
  exact this

lemma cAt_eq {n : ℕ} (p s : ℝ) (A : Fin n) (d : ℕ) :
    cAt n p s A d = (fw n p s (d - 1)).1 / ((fw n p s (d - 1)).1 + (fw n p s (d - 1)).2) := by
  unfold cAt
  rw [(fw_eq n p s A (d - 1)).1, survive_none_eq]

lemma hit_none {n : ℕ} (p s : ℝ) (A : Fin n) (u : ℕ) :
    hitWithin n p s A none u = 1 - (sv n p s u).1 := by
  unfold hitWithin; rw [(survive_eq n p s A u).1]

lemma hit_some {n : ℕ} (p s : ℝ) (A j : Fin n) (hj : j ≠ A) (u : ℕ) :
    hitWithin n p s A (some j) u = 1 - (sv n p s u).2 := by
  unfold hitWithin; rw [(survive_eq n p s A u).2 j hj]

lemma kappa_lt {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p) (hnp : (n : ℝ) * p < 1)
    (t : ℕ) (ht : t ≠ 1) :
    (1 - (n : ℝ) * p) * ((fw n p 1 t).1 + (fw n p 1 t).2) < (fw n p 1 t).1 * (1 - p) := by
  have hnp' := hnp.le
  have hr : 0 < 1 - (n : ℝ) * p := by linarith
  have hw := w_pos hn hp hnp'
  rcases Nat.lt_or_ge t 1 with h | h
  · have : t = 0 := by omega
    subst this
    simp; nlinarith
  · obtain ⟨k, hk⟩ : ∃ k, t = k + 1 + 1 := ⟨t - 2, by omega⟩
    rw [hk]
    have ha := fw_pos_one hn hp hnp' zero_le_one le_rfl hr k
    simp only [fw_succ_fst, fw_succ_snd]
    simp only [sub_self, zero_mul, add_zero, one_mul]
    nlinarith [mul_pos hw ha, mul_pos (mul_pos hw ha) hw]

end UPSol

namespace UPSol
open UniformPatrol.Star

theorem ms_symmetry (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x : PStrat n) (a a' : AStrat n) (hd : a.d = a'.d) :
    Q n m x a = Q n m x a' := by
  rw [Q_eq n m hm, Q_eq n m hm, hd]

theorem ms_lemma_3 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x : PStrat n) (hs : x.s = 1) (a a' : AStrat n)
    (hA : a.A = a'.A) (hd : a.d = 2) :
    Q n m x a ≤ Q n m x a' ∧
    ((n : ℝ) * x.p < 1 → a'.d ≠ 2 → Q n m x a < Q n m x a') := by
  rw [Q_eq n m hm, Q_eq n m hm, hd, hs]
  have hw := w_pos hn x.p_pos x.np_le
  refine ⟨QF_delay_le hn x.p_pos x.np_le zero_le_one le_rfl (by nlinarith) a'.d, ?_⟩
  intro h1 h2
  exact QF_delay_lt hn hm x.p_pos h1 a'.d a'.one_le_d h2

theorem ms_lemma_1 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x x₁ : PStrat n) (hp : x₁.p = x.p) (hs : x₁.s = 1)
    (a : AStrat n) (hd : a.d = 2) :
    Q n m x a ≤ Q n m x₁ a ∧
    (3 ≤ m → x.s < 1 → Q n m x a < Q n m x₁ a) ∧
    (m = 2 → Q n m x a = Q n m x₁ a) ∧
    (m = 2 → ∃ y : PStrat n, y.s < 1 ∧ IsOptimalP n 2 y) := by
  rw [Q_eq n m hm, Q_eq n m hm, hd, hp, hs]
  refine ⟨QF_refl_le hn hm x.p_pos x.np_le x.s_pos.le x.s_le,
    fun h3 hs1 => QF_refl_lt hn h3 x.p_pos x.np_le x.s_pos.le hs1, ?_, ?_⟩
  · rintro rfl; exact QF_m2_indep n x.p x.s
  · rintro rfl
    have h := (thm1_main n 2 hn le_rfl).2.2
    by_contra hc
    push_neg at hc
    have : ∀ y : PStrat n, IsOptimalP n 2 y → y.s = 1 := by
      intro y hy
      by_contra hne
      exact absurd (hc y (lt_of_le_of_ne y.s_le hne)) (not_not.mpr hy)
    have := h.mp this
    omega

theorem ms_start_decomposition (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x : PStrat n) (a : AStrat n) (j : Fin n) (hj : j ≠ a.A) :
    Q n m x a =
      cAt n x.p x.s a.A a.d * hitWithin n x.p x.s a.A none (m - 1) +
      (1 - cAt n x.p x.s a.A a.d) *
        hitWithin n x.p x.s a.A (some j) (m - 1) := by
  rw [Q_eq n m hm, cAt_eq, hit_none, hit_some _ _ _ _ hj]
  unfold QF
  obtain ⟨_, _, h3⟩ := fw_nonneg hn x.p_pos x.np_le x.s_pos.le x.s_le (a.d - 1)
  field_simp
  ring

theorem ms_center_update (n : ℕ) (hn : 2 ≤ n) (x : PStrat n) (A : Fin n) :
    (∀ d : ℕ, 1 ≤ d → cAt n x.p x.s A (d + 1) =
      fMap n x.p x.s (cAt n x.p x.s A d)) ∧
    cAt n x.p x.s A 2 =
      (1 - (n : ℝ) * x.p) / (1 - x.p) ∧
    (x.s = 1 → ∀ d : ℕ, 1 ≤ d →
      cAt n x.p x.s A 2 ≤ cAt n x.p x.s A d) ∧
    (x.s = 1 → (n : ℝ) * x.p < 1 → ∀ d : ℕ, 1 ≤ d → d ≠ 2 →
      cAt n x.p x.s A 2 < cAt n x.p x.s A d) := by
  have hq := one_sub_p_pos hn x.p_pos x.np_le
  have hc2 : cAt n x.p x.s A 2 = (1 - (n : ℝ) * x.p) / (1 - x.p) := by
    rw [cAt_eq]
    simp only [show 2 - 1 = 0 + 1 from rfl, fw_succ_fst, fw_succ_snd, fw_zero]
    congr 1 <;> ring
  refine ⟨?_, hc2, ?_, ?_⟩
  · intro d hd
    rw [cAt_eq, cAt_eq]
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    obtain ⟨g1, g2, g3⟩ := fw_nonneg hn x.p_pos x.np_le x.s_pos.le x.s_le k
    simp only [fw_succ_fst, fw_succ_snd]
    unfold fMap
    set α := (fw n x.p x.s k).1
    set β := (fw n x.p x.s k).2
    have hS : α + β ≠ 0 := g3.ne'
    have hD : 0 < (1 - x.p) * α + β := by
      rcases lt_or_eq_of_le g2 with hb | hb
      · nlinarith [mul_nonneg hq.le g1]
      · have : 0 < α := by linarith
        nlinarith [mul_pos hq this]
    have e : 1 - x.p * (α / (α + β)) = ((1 - x.p) * α + β) / (α + β) := by
      field_simp; ring
    rw [e]
    have e2 : α / (α + β) * (1 - (n : ℝ) * x.p) + (1 - α / (α + β)) * x.s =
        ((1 - (n : ℝ) * x.p) * α + x.s * β) / (α + β) := by
      field_simp; ring
    rw [e2, div_div_div_cancel_right₀ hS]
    congr 1; ring
  · intro hs d _
    rw [hc2, cAt_eq]
    obtain ⟨_, _, g3⟩ := fw_nonneg hn x.p_pos x.np_le x.s_pos.le x.s_le (d - 1)
    have hk : 1 - (n : ℝ) * x.p ≤ x.s * (1 - x.p) := by
      rw [hs]; have := w_pos hn x.p_pos x.np_le; nlinarith
    have := fw_kappa hn x.p_pos x.np_le x.s_pos.le x.s_le hk (d - 1)
    rw [div_le_div_iff₀ hq g3]
    linarith
  · intro hs hnp d hd1 hd2
    rw [hc2, cAt_eq]
    obtain ⟨_, _, g3⟩ := fw_nonneg hn x.p_pos x.np_le x.s_pos.le x.s_le (d - 1)
    have := kappa_lt hn x.p_pos hnp (d - 1) (by omega)
    rw [hs] at g3 ⊢
    rw [div_lt_div_iff₀ hq g3]
    linarith

theorem ms_lemma_2 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x : PStrat n) (A j : Fin n) (hj : j ≠ A) :
    hitWithin n x.p x.s A (some j) (m - 1) ≤
      hitWithin n x.p x.s A none (m - 1) ∧
    (hitWithin n x.p x.s A (some j) (m - 1) =
      hitWithin n x.p x.s A none (m - 1) ↔
      x.s = 1 ∧ (n : ℝ) * x.p = 1 ∧ Odd m) := by
  rw [hit_none, hit_some _ _ _ _ hj]
  have hCE := sv_C_le_E hn x.p_pos x.np_le x.s_pos.le x.s_le (m - 1)
  refine ⟨by linarith, ?_⟩
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  constructor
  · intro heq
    have heq' : (sv n x.p x.s (m - 1)).1 = (sv n x.p x.s (m - 1)).2 := by linarith
    have hs : x.s = 1 := by
      by_contra hne
      have := sv_C_lt_E_s hn x.p_pos x.np_le x.s_pos.le (lt_of_le_of_ne x.s_le hne) (m - 1) (by omega)
      linarith
    have hr : (n : ℝ) * x.p = 1 := by
      by_contra hne
      have hr : 0 < 1 - (n : ℝ) * x.p := by
        rcases lt_or_eq_of_le x.np_le with h | h
        · linarith
        · exact absurd h hne
      have := sv_C_lt_E hn x.p_pos x.np_le x.s_pos.le x.s_le hr (m - 1) (by omega)
      linarith
    refine ⟨hs, hr, ?_⟩
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨i, hi⟩ := hodd
    have hp : x.p = 1 / n := by field_simp; linarith
    rw [hs, hp] at heq'
    have hmi : m - 1 = 2 * (i - 1) + 1 := by omega
    rw [hmi, (sv_exact hn (i - 1)).2.1, (sv_exact hn (i - 1)).2.2.2, pow_succ] at heq'
    obtain ⟨hq0, hq1, hqn⟩ := q_facts hn
    have hqpos : 0 < ((n : ℝ) - 1) / n := div_pos (by linarith) hn0
    have hqlt : ((n : ℝ) - 1) / n < 1 := by rw [div_lt_one hn0]; linarith
    have hX : 0 < (((n : ℝ) - 1) / n) ^ (i - 1) := pow_pos hqpos _
    nlinarith
  · rintro ⟨hs, hr, ⟨j', hj'⟩⟩
    have hp : x.p = 1 / n := by field_simp; linarith
    have hmj : m - 1 = 2 * j' := by omega
    rw [hs, hp, hmj, (sv_exact hn j').1, (sv_exact hn j').2.2.1]

theorem ms_even_interior (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (he : Even m) :
    ∃ x : PStrat n, x.s = 1 ∧ (n : ℝ) * x.p < 1 ∧
      ∀ x' : PStrat n, x'.s = 1 → ∀ a : AStrat n, a.d = 2 →
        Q n m x' a ≤ Q n m x a := by
  obtain ⟨ps, hps, hnps, hmax, heven⟩ := exists_max hn hm
  refine ⟨⟨ps, 1, hps, hnps, one_pos, le_rfl⟩, rfl, heven he, fun x' hs a ha => ?_⟩
  rw [Q_eq n m hm, Q_eq n m hm, ha, hs]
  exact hmax x'.p x'.p_pos x'.np_le

theorem ms_proposition_2 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (ho : Odd m) :
    ∃ x : PStrat n, x.p = 1 / (n : ℝ) ∧ x.s = 1 ∧
      (∀ a : AStrat n, IsSaddle n m x a) ∧
      (∀ a : AStrat n,
        Q n m x a = 1 - (((n : ℝ) - 1) / (n : ℝ)) ^ ((m - 1) / 2)) ∧
      (∀ x' : PStrat n, IsOptimalP n m x' →
        x'.p = 1 / (n : ℝ) ∧ x'.s = 1) := by
  obtain ⟨j, hj⟩ := ho
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let x1 : PStrat n := ⟨1 / n, 1, by positivity, by field_simp; rfl, one_pos, le_rfl⟩
  have hval : ∀ a : AStrat n, Q n m x1 a = 1 - (((n : ℝ) - 1) / (n : ℝ)) ^ j := by
    intro a; rw [Q_eq n m hm]; exact QF_odd_eq hn j hj a.d
  have hub : ∀ (x' : PStrat n) (a : AStrat n), Q n m x' a ≤ 1 - (((n : ℝ) - 1) / (n : ℝ)) ^ j := by
    intro x' a; rw [Q_eq n m hm]
    exact QF_odd_le hn j hj x'.p_pos x'.np_le x'.s_pos.le x'.s_le a.d
  have hj2 : (m - 1) / 2 = j := by omega
  have hsad : ∀ a : AStrat n, IsSaddle n m x1 a := by
    intro a
    refine ⟨fun x' => by rw [hval]; exact hub x' a, fun a' => by rw [hval, hval]⟩
  refine ⟨x1, rfl, rfl, hsad, fun a => by rw [hj2]; exact hval a, ?_⟩
  intro x' ⟨a, hx⟩
  have hA0 : 0 < n := by omega
  -- every attack gives the value against x'
  have hall : ∀ a' : AStrat n, Q n m x' a' = 1 - (((n : ℝ) - 1) / (n : ℝ)) ^ j := by
    intro a'
    have c1 := hx.1 x1
    have c2 := hx.2 a'
    rw [hval] at c1
    linarith [hub x' a']
  have hm3 : 3 ≤ m := by omega
  let a2 : AStrat n := ⟨⟨0, hA0⟩, 2, by norm_num⟩
  let a1 : AStrat n := ⟨⟨0, hA0⟩, 1, le_rfl⟩
  have hs : x'.s = 1 := by
    by_contra hne
    have hlt := QF_refl_lt hn hm3 x'.p_pos x'.np_le x'.s_pos.le (lt_of_le_of_ne x'.s_le hne)
    have e2 := hall a2
    rw [Q_eq n m hm] at e2
    have := QF_odd_le hn j hj x'.p_pos x'.np_le zero_le_one le_rfl 2
    change QF n m x'.p x'.s 2 = _ at e2
    linarith
  refine ⟨?_, hs⟩
  by_contra hne
  have hnp : (n : ℝ) * x'.p < 1 := by
    rcases lt_or_eq_of_le x'.np_le with h | h
    · exact h
    · exfalso; apply hne; field_simp; linarith
  have hlt := QF_delay_lt hn hm x'.p_pos hnp 1 le_rfl (by norm_num)
  have e1 := hall a1
  have e2 := hall a2
  rw [Q_eq n m hm, hs] at e1 e2
  change QF n m x'.p 1 1 = _ at e1
  change QF n m x'.p 1 2 = _ at e2
  linarith

end UPSol

open UniformPatrol.Star in
theorem solution (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (ho : Odd m) :
    ∃ x : PStrat n, x.p = 1 / (n : ℝ) ∧ x.s = 1 ∧
      (∀ a : AStrat n, IsSaddle n m x a) ∧
      (∀ a : AStrat n,
        Q n m x a = 1 - (((n : ℝ) - 1) / (n : ℝ)) ^ ((m - 1) / 2)) ∧
      (∀ x' : PStrat n, IsOptimalP n m x' →
        x'.p = 1 / (n : ℝ) ∧ x'.s = 1) := by
  apply UPSol.ms_proposition_2 <;> assumption
