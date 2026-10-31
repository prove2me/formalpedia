-- Prove2me | solution 1 for RemanProcure.Noncongestive.lemma_1_preserve
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:40:28.322209+00:00
-- url     : https://prove2.me/submissions/423e328d-56b6-41db-9783-8c5edf88502c

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model

open RemanProcure.Noncongestive

/-- Weighted sums respect pointwise inequalities with a constant slack (since `∑ p = 1`). -/
lemma reman_wsum {K : ℕ} (p : Fin K → ℝ) (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (f g : Fin K → ℝ) (c : ℝ) (h : ∀ j, f j ≤ g j + c) :
    ∑ j, p j * f j ≤ ∑ j, p j * g j + c := by
  have : ∑ j, p j * f j ≤ ∑ j, p j * (g j + c) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hp j)
  have e : ∑ j, p j * (g j + c) = ∑ j, p j * g j + c := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hps, one_mul]
  linarith

lemma reman_wsum2 {K : ℕ} (p : Fin K → ℝ) (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (f1 f2 g1 g2 : Fin K → ℝ) (c : ℝ) (h : ∀ j, f1 j + f2 j ≤ g1 j + g2 j + c) :
    ∑ j, p j * f1 j + ∑ j, p j * f2 j ≤ ∑ j, p j * g1 j + ∑ j, p j * g2 j + c := by
  have := reman_wsum p hp hps (fun j => f1 j + f2 j) (fun j => g1 j + g2 j) c h
  simp only [mul_add, Finset.sum_add_distrib] at this
  linarith

lemma reman_filter_sum {K : ℕ} (l : Fin K) (f : Fin K → ℝ) :
    ∑ j, f j = ∑ i ∈ Finset.univ.filter (· ≤ l), f i + ∑ i ∈ Finset.univ.filter (l < ·), f i := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ l)]
  congr 1
  apply Finset.sum_congr
  · ext i; simp [not_le]
  · intro i _; rfl

lemma reman_sum_le {K : ℕ} (s : Finset (Fin K)) (p : Fin K → ℝ) (hp : ∀ i, 0 ≤ p i)
    (a b c : Fin K → ℝ) (h : ∀ i ∈ s, a i - b i ≥ c i) :
    ∑ i ∈ s, p i * a i - ∑ i ∈ s, p i * b i ≥ ∑ i ∈ s, p i * c i := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left (h i hi) (hp i)

theorem remanT1_VA {K : ℕ} (P : Params K) (hP : Standing P) (v : (Fin K → ℕ) → ℝ) (hv : VA P v) : VA P (T1 P v) := by
  obtain ⟨hK, hp, hps, hrm, -, -, -, hrc, -⟩ := hP
  obtain ⟨A1, A2, A3, A4, A5, A6⟩ := hv
  set W : (Fin K → ℕ) → ℝ := fun y => P.cA + ∑ j, P.p j * v (y + e j) with hWdef
  have hT1 : ∀ y, T1 P v y = min (v y) (W y) := fun y => rfl
  have l0 : Fin K := ⟨0, hK⟩
  set o : Fin K := ⟨0, hK⟩ with ho
  have hmin : ∀ i : Fin K, o ≤ i := fun i => by simp [ho, Fin.le_def]
  -- (A.5)/(A.6) at l = 1 in the form of sums over all types
  have key : ∀ y : Fin K → ℕ,
      (∑ i ∈ Finset.univ.filter (· ≤ o), P.p i * v (y + e o))
        + (∑ i ∈ Finset.univ.filter (o < ·), P.p i * v (y + e i))
        = ∑ i, P.p i * v (y + e i) := by
    intro y
    rw [reman_filter_sum o (fun i => P.p i * v (y + e i))]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have : i = o := le_antisymm hi (hmin i)
    rw [this]
  have comm2 : ∀ (y : Fin K → ℕ) (a b : Fin K), y + e a + e b = y + e b + e a :=
    fun y a b => add_right_comm _ _ _
  -- Δ monotone: W - v nondecreasing in each coordinate
  have dmono : ∀ (y : Fin K → ℕ) (q : Fin K), W y - v y ≤ W (y + e q) - v (y + e q) := by
    intro y q
    have h := A5 y o q (hmin q)
    rw [key, key] at h
    simp only [hWdef]
    linarith
  have dA6 : ∀ (y : Fin K → ℕ) (q w : Fin K), q ≤ w → W (y + e w) - v (y + e w) ≤ W (y + e q) - v (y + e q) := by
    intro y q w hqw
    rcases eq_or_lt_of_le hqw with h | h
    · rw [h]
    have h := A6 y o q w (hmin q) h
    rw [key, key] at h
    simp only [hWdef]
    linarith
  have hT1le : ∀ y, T1 P v y ≤ v y ∧ T1 P v y ≤ W y := fun y => ⟨min_le_left _ _, min_le_right _ _⟩
  have hT1cases : ∀ y, (T1 P v y = v y ∧ v y ≤ W y) ∨ (T1 P v y = W y ∧ W y ≤ v y) := by
    intro y
    rw [hT1]
    rcases le_total (v y) (W y) with h | h
    · left; exact ⟨min_eq_left h, h⟩
    · right; exact ⟨min_eq_right h, h⟩
  have pp := hp
  -- difference of W written as weighted sum
  have Wdiff : ∀ a b : Fin K → ℕ, W a - W b = ∑ j, P.p j * v (a + e j) - ∑ j, P.p j * v (b + e j) := by
    intro a b; simp only [hWdef]; ring
  -- lower bounds on differences of T1
  have L1 : ∀ (y : Fin K → ℕ) (q : Fin K), T1 P v (y + e q) - T1 P v y ≥ v (y + e q) - v y := by
    intro y q
    rcases hT1cases (y + e q) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; linarith [(hT1le y).1]
    · rw [h]; linarith [(hT1le y).2, dmono y q]
  have L2 : ∀ (y : Fin K → ℕ) (q w : Fin K), q ≤ w →
      T1 P v (y + e q) - T1 P v (y + e w) ≥ v (y + e q) - v (y + e w) := by
    intro y q w hqw
    rcases hT1cases (y + e q) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; linarith [(hT1le (y + e w)).1]
    · rw [h]; linarith [(hT1le (y + e w)).2, dA6 y q w hqw]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (A.1)
    intro x w
    rcases hT1cases (x + e w) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; linarith [(hT1le x).1, A1 x w]
    · rw [h]
      have hs := reman_wsum P.p hp hps (fun j => v (x + e j) + P.r w) (fun j => v (x + e w + e j))
        P.cL (fun j => by have := A1 (x + e j) w; rw [comm2] at this; linarith)
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hps, one_mul] at hs
      have := (hT1le x).2
      simp only [hWdef] at this ⊢
      linarith
  · -- (A.2)
    intro x q w hqw
    rcases hT1cases (x + e q) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; linarith [(hT1le (x + e w)).1, A2 x q w hqw]
    · rw [h]
      have hs := reman_wsum P.p hp hps (fun j => v (x + e w + e j) + P.r q)
        (fun j => v (x + e q + e j) + P.r w) 0 (fun j => by
          have := A2 (x + e j) q w hqw; rw [comm2 x j q, comm2 x j w] at this; linarith)
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hps, one_mul] at hs
      have := (hT1le (x + e w)).2
      simp only [hWdef] at this ⊢
      linarith
  · -- (A.3)
    intro x d l q hdl hlq
    have F1 := A3 x d l q hdl hlq
    have F2 := reman_wsum2 P.p hp hps (fun j => v (x + e l + e j)) (fun j => v (x + e q + e d + e j))
      (fun j => v (x + e q + e l + e j)) (fun j => v (x + e d + e j)) 0 (fun j => by
        have := A3 (x + e j) d l q hdl hlq
        have r1 : x + e j + e q + e l = x + e q + e l + e j := by abel
        have r2 : x + e j + e q + e d = x + e q + e d + e j := by abel
        rw [r1, r2, comm2 x j l, comm2 x j d] at this; linarith)
    have F3 := dmono (x + e l) q
    rw [comm2 x l q] at F3
    have F4 := dA6 x d l hdl
    have Wa := Wdiff (x + e q + e l) (x + e q + e d)
    have Wb := Wdiff (x + e l) (x + e d)
    rcases hT1cases (x + e q + e l) with ⟨ha, -⟩ | ⟨ha, -⟩ <;>
    rcases hT1cases (x + e d) with ⟨hd, -⟩ | ⟨hd, -⟩ <;>
    · rw [ha, hd]
      linarith [hT1le (x + e q + e d), hT1le (x + e l)]
  · -- (A.4)
    intro x d l q w hdl hlq hqw
    have F1 := A4 x d l q w hdl hlq hqw
    have F2 := reman_wsum2 P.p hp hps (fun j => v (x + e w + e l + e j)) (fun j => v (x + e q + e d + e j))
      (fun j => v (x + e q + e l + e j)) (fun j => v (x + e w + e d + e j)) 0 (fun j => by
        have := A4 (x + e j) d l q w hdl hlq hqw
        have r1 : x + e j + e q + e l = x + e q + e l + e j := by abel
        have r2 : x + e j + e q + e d = x + e q + e d + e j := by abel
        have r3 : x + e j + e w + e l = x + e w + e l + e j := by abel
        have r4 : x + e j + e w + e d = x + e w + e d + e j := by abel
        rw [r1, r2, r3, r4] at this; linarith)
    have F3 := dA6 (x + e l) q w hqw
    rw [comm2 x l q, comm2 x l w] at F3
    have F4 := dA6 (x + e w) d l hdl
    have Wa := Wdiff (x + e q + e l) (x + e q + e d)
    have Wb := Wdiff (x + e w + e l) (x + e w + e d)
    rcases hT1cases (x + e q + e l) with ⟨ha, -⟩ | ⟨ha, -⟩ <;>
    rcases hT1cases (x + e w + e d) with ⟨hd, -⟩ | ⟨hd, -⟩ <;>
    · rw [ha, hd]
      linarith [hT1le (x + e q + e d), hT1le (x + e w + e l)]
  · -- (A.5)
    intro x l q hlq
    have s1 := reman_sum_le (Finset.univ.filter (· ≤ l)) P.p hp
      (fun _ => T1 P v (x + e q + e l)) (fun _ => T1 P v (x + e l))
      (fun _ => v (x + e q + e l) - v (x + e l)) (fun i _ => by
        have := L1 (x + e l) q; rw [comm2 x l q] at this; exact this)
    have s2 := reman_sum_le (Finset.univ.filter (l < ·)) P.p hp
      (fun i => T1 P v (x + e q + e i)) (fun i => T1 P v (x + e i))
      (fun i => v (x + e q + e i) - v (x + e i)) (fun i _ => by
        have := L1 (x + e i) q; rw [comm2 x i q] at this; exact this)
    try simp only at s1 s2
    have hv5 := A5 x l q hlq
    rcases hT1cases x with ⟨hx, -⟩ | ⟨hx, -⟩
    · rw [hx]
      have := (hT1le (x + e q)).1
      have e1 := (Finset.sum_sub_distrib (s := Finset.univ.filter (· ≤ l))
        (f := fun i => P.p i * v (x + e q + e l)) (g := fun i => P.p i * v (x + e l)))
      have e2 := (Finset.sum_sub_distrib (s := Finset.univ.filter (l < ·))
        (f := fun i => P.p i * v (x + e q + e i)) (g := fun i => P.p i * v (x + e i)))
      simp only [← mul_sub] at e1 e2
      linarith
    · rw [hx]
      have := (hT1le (x + e q)).2
      have hW := Wdiff (x + e q) x
      have s3 := reman_sum_le (Finset.univ.filter (· ≤ l)) P.p hp
        (fun _ => v (x + e q + e l) - v (x + e l)) (fun i => v (x + e q + e i) - v (x + e i))
        (fun _ => 0) (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have := A3 x i l q hi hlq; linarith)
      simp only [mul_zero, Finset.sum_const_zero] at s3
      have e3 := reman_filter_sum l (fun i => P.p i * v (x + e q + e i))
      have e4 := reman_filter_sum l (fun i => P.p i * v (x + e i))
      simp only [mul_sub, Finset.sum_sub_distrib] at s1 s2 s3
      simp only [hWdef] at this hW ⊢
      linarith
  · -- (A.6)
    intro x l q w hlq hqw
    have s1 := reman_sum_le (Finset.univ.filter (· ≤ l)) P.p hp
      (fun _ => T1 P v (x + e q + e l)) (fun _ => T1 P v (x + e w + e l))
      (fun _ => v (x + e q + e l) - v (x + e w + e l)) (fun i _ => by
        have := L2 (x + e l) q w hqw.le; rw [comm2 x l q, comm2 x l w] at this; exact this)
    have s2 := reman_sum_le (Finset.univ.filter (l < ·)) P.p hp
      (fun i => T1 P v (x + e q + e i)) (fun i => T1 P v (x + e w + e i))
      (fun i => v (x + e q + e i) - v (x + e w + e i)) (fun i _ => by
        have := L2 (x + e i) q w hqw.le; rw [comm2 x i q, comm2 x i w] at this; exact this)
    try simp only at s1 s2
    have hv6 := A6 x l q w hlq hqw
    simp only [mul_sub, Finset.sum_sub_distrib] at s1 s2
    rcases hT1cases (x + e w) with ⟨hx, -⟩ | ⟨hx, -⟩
    · rw [hx]
      have := (hT1le (x + e q)).1
      linarith
    · rw [hx]
      have := (hT1le (x + e q)).2
      have hW := Wdiff (x + e q) (x + e w)
      have s3 := reman_sum_le (Finset.univ.filter (· ≤ l)) P.p hp
        (fun _ => v (x + e q + e l) - v (x + e w + e l)) (fun i => v (x + e q + e i) - v (x + e w + e i))
        (fun _ => 0) (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have := A4 x i l q w hi hlq hqw.le; linarith)
      simp only [mul_zero, Finset.sum_const_zero, mul_sub, Finset.sum_sub_distrib] at s3
      have e3 := reman_filter_sum l (fun i => P.p i * v (x + e q + e i))
      have e4 := reman_filter_sum l (fun i => P.p i * v (x + e w + e i))
      simp only [hWdef] at this hW ⊢
      linarith


lemma remanT2_add_e_sub {K : ℕ} (y : Fin K → ℕ) (j : Fin K) : y + e j - e j = y := by
  ext k; simp [e, Pi.single_apply]

lemma remanT2_sub_e_add {K : ℕ} (y : Fin K → ℕ) (j : Fin K) (h : 0 < y j) : y - e j + e j = y := by
  ext k
  simp only [Pi.add_apply, Pi.sub_apply, e, Pi.single_apply]
  split_ifs with hk
  · subst hk; omega
  · simp

lemma remanT2_ge_add {K : ℕ} (y : Fin K → ℕ) (c k : Fin K) (hy : ∀ j, 0 < y j → c ≤ j)
    (hck : c ≤ k) : ∀ j, 0 < (y + e k) j → c ≤ j := by
  intro j hj
  by_cases hjk : j = k
  · subst hjk; exact hck
  · apply hy j
    simpa [e, Pi.single_apply, hjk] using hj

lemma remanT2_ge_zero {K : ℕ} (c : Fin K) : ∀ j, 0 < (0 : Fin K → ℕ) j → c ≤ j := by
  intro j hj; simp at hj

lemma remanT2_ge_mono {K : ℕ} (y : Fin K → ℕ) (b c : Fin K) (hy : ∀ j, 0 < y j → b ≤ j)
    (hcb : c ≤ b) : ∀ j, 0 < y j → c ≤ j := fun j hj => le_trans hcb (hy j hj)

lemma remanT2_decomp {K : ℕ} (x : Fin K → ℕ) :
    x = 0 ∨ ∃ (b : Fin K) (x' : Fin K → ℕ), x = x' + e b ∧ ∀ j, 0 < x' j → b ≤ j := by
  by_cases h : ∃ j, 0 < x j
  · right
    have hs : (Finset.univ.filter (fun j => 0 < x j)).Nonempty := by
      obtain ⟨j, hj⟩ := h; exact ⟨j, by simp [hj]⟩
    set b := (Finset.univ.filter (fun j => 0 < x j)).min' hs
    have hb : 0 < x b := by
      have := Finset.min'_mem _ hs
      simpa using this
    refine ⟨b, x - e b, (remanT2_sub_e_add x b hb).symm, ?_⟩
    intro j hj
    have hxj : 0 < x j := by
      simp only [Pi.sub_apply] at hj; omega
    exact Finset.min'_le _ _ (by simp [hxj])
  · left
    push Not at h
    ext j; simp only [Pi.zero_apply]; have := h j; omega

lemma remanT2_decompC {K : ℕ} (x : Fin K → ℕ) (c : Fin K) :
    (∀ j, 0 < x j → c ≤ j) ∨ ∃ (b : Fin K) (x' : Fin K → ℕ), x = x' + e b ∧
      (∀ j, 0 < x' j → b ≤ j) ∧ b < c := by
  rcases remanT2_decomp x with rfl | ⟨b, x', rfl, hx'⟩
  · left; exact remanT2_ge_zero c
  · by_cases hcb : c ≤ b
    · left; exact remanT2_ge_add _ _ _ (remanT2_ge_mono _ _ _ hx' hcb) hcb
    · right; exact ⟨b, x', rfl, hx', lt_of_not_ge hcb⟩

lemma remanT2_up {K : ℕ} (P : Params K) (v : (Fin K → ℕ) → ℝ) (y : Fin K → ℕ) (j : Fin K) :
    T2 P v (y + e j) ≤ v y + P.r j := by
  unfold T2
  rw [Finset.fold_min_le]
  right
  refine ⟨j, Finset.mem_univ _, ?_⟩
  have h1 : 0 < (y + e j) j := by simp [e]
  rw [if_pos h1, remanT2_add_e_sub]

lemma remanT2_upL {K : ℕ} (P : Params K) (v : (Fin K → ℕ) → ℝ) (z : Fin K → ℕ) :
    T2 P v z ≤ v z + P.cL := by
  unfold T2
  rw [Finset.fold_min_le]
  left; exact le_rfl

lemma remanT2_zero {K : ℕ} (P : Params K) (v : (Fin K → ℕ) → ℝ) :
    T2 P v 0 = v 0 + P.cL := by
  apply le_antisymm (remanT2_upL P v 0)
  unfold T2
  rw [Finset.le_fold_min]
  refine ⟨le_rfl, fun i _ => ?_⟩
  simp

lemma remanT2_exact {K : ℕ} (P : Params K) (v : (Fin K → ℕ) → ℝ)
    (A1 : ∀ (x : Fin K → ℕ) (w : Fin K), v (x + e w) + P.cL ≥ v x + P.r w)
    (A2 : ∀ (x : Fin K → ℕ) (q w : Fin K), q < w → v (x + e q) + P.r w ≥ v (x + e w) + P.r q)
    (y : Fin K → ℕ) (b : Fin K) (hy : ∀ j, 0 < y j → b ≤ j) :
    T2 P v (y + e b) = v y + P.r b := by
  apply le_antisymm (remanT2_up P v y b)
  unfold T2
  rw [Finset.le_fold_min]
  refine ⟨by linarith [A1 y b], fun j _ => ?_⟩
  split_ifs with hj
  · by_cases hjb : j = b
    · subst hjb; rw [remanT2_add_e_sub]
    · have hyj : 0 < y j := by
        simpa [e, Pi.single_apply, hjb] using hj
      have hbj : b < j := lt_of_le_of_ne (hy j hyj) (Ne.symm hjb)
      have hy' : y = (y - e j) + e j := (remanT2_sub_e_add y j hyj).symm
      have h2 : y + e b - e j = (y - e j) + e b := by
        conv_lhs => rw [hy']
        rw [add_right_comm, remanT2_add_e_sub]
      rw [h2]
      have := A2 (y - e j) b j hbj
      rw [← hy'] at this
      linarith
  · linarith [A1 y b]

lemma remanT2_filter_sum {K : ℕ} (l : Fin K) (f : Fin K → ℝ) :
    ∑ j, f j = ∑ i ∈ Finset.univ.filter (· ≤ l), f i + ∑ i ∈ Finset.univ.filter (l < ·), f i := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ l)]
  congr 1
  apply Finset.sum_congr
  · ext i; simp [not_le]
  · intro i _; rfl

lemma remanT2_sform {K : ℕ} (p φ : Fin K → ℝ) (l : Fin K) :
    (∑ i ∈ Finset.univ.filter (· ≤ l), p i * φ l) + (∑ i ∈ Finset.univ.filter (l < ·), p i * φ i)
      = ∑ i, p i * φ (max i l) := by
  rw [remanT2_filter_sum l (fun i => p i * φ (max i l))]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [max_eq_right hi]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [max_eq_left hi.le]

lemma remanT2_wsum {K : ℕ} (p : Fin K → ℝ) (hp : ∀ i, 0 ≤ p i) (a b c : Fin K → ℝ)
    (h : ∀ i, c i ≤ a i - b i) : ∑ i, p i * c i ≤ ∑ i, p i * a i - ∑ i, p i * b i := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left (h i) (hp i)

lemma remanT2_A5form {K : ℕ} (P : Params K) (g : (Fin K → ℕ) → ℝ) (x : Fin K → ℕ) (l q : Fin K) :
    ((∑ i ∈ Finset.univ.filter (· ≤ l), P.p i * g (x + e q + e l))
      + (∑ i ∈ Finset.univ.filter (l < ·), P.p i * g (x + e q + e i)) - g (x + e q)
    ≥ (∑ i ∈ Finset.univ.filter (· ≤ l), P.p i * g (x + e l))
      + (∑ i ∈ Finset.univ.filter (l < ·), P.p i * g (x + e i)) - g x) ↔
    (∑ i, P.p i * g (x + e q + e (max i l)) - g (x + e q) ≥
      ∑ i, P.p i * g (x + e (max i l)) - g x) := by
  have s1 := remanT2_sform P.p (fun m => g (x + e q + e m)) l
  have s2 := remanT2_sform P.p (fun m => g (x + e m)) l
  rw [s1, s2]

lemma remanT2_A6form {K : ℕ} (P : Params K) (g : (Fin K → ℕ) → ℝ) (x : Fin K → ℕ) (l q w : Fin K) :
    ((∑ i ∈ Finset.univ.filter (· ≤ l), P.p i * g (x + e q + e l))
      + (∑ i ∈ Finset.univ.filter (l < ·), P.p i * g (x + e q + e i)) - g (x + e q)
    ≥ (∑ i ∈ Finset.univ.filter (· ≤ l), P.p i * g (x + e w + e l))
      + (∑ i ∈ Finset.univ.filter (l < ·), P.p i * g (x + e w + e i)) - g (x + e w)) ↔
    (∑ i, P.p i * g (x + e q + e (max i l)) - g (x + e q) ≥
      ∑ i, P.p i * g (x + e w + e (max i l)) - g (x + e w)) := by
  have s1 := remanT2_sform P.p (fun m => g (x + e q + e m)) l
  have s2 := remanT2_sform P.p (fun m => g (x + e w + e m)) l
  rw [s1, s2]

theorem remanT2_VA {K : ℕ} (P : Params K) (hP : Standing P) (v : (Fin K → ℕ) → ℝ) (hv : VA P v) :
    VA P (T2 P v) := by
  obtain ⟨-, hp, hps, -, -, -, -, -, -⟩ := hP
  obtain ⟨A1, A2, A3, A4, A5, A6⟩ := hv
  have ex := remanT2_exact P v A1 A2
  have up := remanT2_up P v
  have upL := remanT2_upL P v
  have A5' : ∀ (x : Fin K → ℕ) (l q : Fin K), l ≤ q →
      ∑ i, P.p i * v (x + e q + e (max i l)) - v (x + e q) ≥
      ∑ i, P.p i * v (x + e (max i l)) - v x :=
    fun x l q h => (remanT2_A5form P v x l q).1 (A5 x l q h)
  have A6' : ∀ (x : Fin K → ℕ) (l q w : Fin K), l ≤ q → q < w →
      ∑ i, P.p i * v (x + e q + e (max i l)) - v (x + e q) ≥
      ∑ i, P.p i * v (x + e w + e (max i l)) - v (x + e w) :=
    fun x l q w h1 h2 => (remanT2_A6form P v x l q w).1 (A6 x l q w h1 h2)
  have hconst : ∀ k : ℝ, ∑ i, P.p i * k = k := fun k => by
    rw [← Finset.sum_mul, hps, one_mul]
  have gadd := @remanT2_ge_add K
  have gmono := @remanT2_ge_mono K
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (A.1)
    intro x w
    rcases remanT2_decompC x w with hx | ⟨b, x', rfl, hx', hbw⟩
    · have h1 := ex x w hx
      have h2 := upL x
      linarith
    · have h1 : T2 P v (x' + e b + e w) = v (x' + e w) + P.r b := by
        rw [show x' + e b + e w = x' + e w + e b by abel]
        exact ex _ _ (gadd _ _ _ hx' hbw.le)
      have h2 := up x' b
      have := A1 x' w
      linarith
  · -- (A.2)
    intro x q w hqw
    rcases remanT2_decompC x q with hx | ⟨b, x', rfl, hx', hbq⟩
    · have h1 := ex x q hx
      have h2 := up x w
      linarith
    · have h1 : T2 P v (x' + e b + e q) = v (x' + e q) + P.r b := by
        rw [show x' + e b + e q = x' + e q + e b by abel]
        exact ex _ _ (gadd _ _ _ hx' hbq.le)
      have h2 : T2 P v (x' + e b + e w) ≤ v (x' + e w) + P.r b := by
        rw [show x' + e b + e w = x' + e w + e b by abel]; exact up _ _
      have := A2 x' q w hqw
      linarith
  · -- (A.3)
    intro x d l q hdl hlq
    rcases remanT2_decompC x l with hx | ⟨b, x', rfl, hx', hbl⟩
    · have h1 := ex (x + e q) l (gadd _ _ _ hx hlq)
      have h2 := ex x d (gmono _ _ _ hx hdl)
      have h3 := up (x + e q) d
      have h4 := up x l
      linarith
    · have h1 : T2 P v (x' + e b + e q + e l) = v (x' + e q + e l) + P.r b := by
        rw [show x' + e b + e q + e l = x' + e q + e l + e b by abel]
        exact ex _ _ (gadd _ _ _ (gadd _ _ _ hx' (hbl.le.trans hlq)) hbl.le)
      have h4 : T2 P v (x' + e b + e l) ≤ v (x' + e l) + P.r b := by
        rw [show x' + e b + e l = x' + e l + e b by abel]; exact up _ _
      by_cases hdb : d ≤ b
      · have h2 := ex (x' + e b) d (gadd _ _ _ (gmono _ _ _ hx' hdb) hdb)
        have h3 := up (x' + e b + e q) d
        have := A3 x' b l q hbl.le hlq
        have hc : x' + e b + e q = x' + e q + e b := by abel
        rw [← hc] at this
        linarith
      · have hbd : b < d := lt_of_not_ge hdb
        have h2 : T2 P v (x' + e b + e d) = v (x' + e d) + P.r b := by
          rw [show x' + e b + e d = x' + e d + e b by abel]
          exact ex _ _ (gadd _ _ _ hx' hbd.le)
        have h3 : T2 P v (x' + e b + e q + e d) ≤ v (x' + e q + e d) + P.r b := by
          rw [show x' + e b + e q + e d = x' + e q + e d + e b by abel]; exact up _ _
        have := A3 x' d l q hdl hlq
        linarith
  · -- (A.4)
    intro x d l q w hdl hlq hqw
    rcases remanT2_decompC x l with hx | ⟨b, x', rfl, hx', hbl⟩
    · have h1 := ex (x + e q) l (gadd _ _ _ hx hlq)
      have h2 := ex (x + e w) d (gadd _ _ _ (gmono _ _ _ hx hdl) (hdl.trans (hlq.trans hqw)))
      have h3 := up (x + e q) d
      have h4 := up (x + e w) l
      linarith
    · have h1 : T2 P v (x' + e b + e q + e l) = v (x' + e q + e l) + P.r b := by
        rw [show x' + e b + e q + e l = x' + e q + e l + e b by abel]
        exact ex _ _ (gadd _ _ _ (gadd _ _ _ hx' (hbl.le.trans hlq)) hbl.le)
      have h4 : T2 P v (x' + e b + e w + e l) ≤ v (x' + e w + e l) + P.r b := by
        rw [show x' + e b + e w + e l = x' + e w + e l + e b by abel]; exact up _ _
      by_cases hdb : d ≤ b
      · have h2 := ex (x' + e b + e w) d
          (gadd _ _ _ (gadd _ _ _ (gmono _ _ _ hx' hdb) hdb) (hdl.trans (hlq.trans hqw)))
        have h3 := up (x' + e b + e q) d
        have := A4 x' b l q w hbl.le hlq hqw
        have hc : x' + e b + e q = x' + e q + e b := by abel
        have hc2 : x' + e b + e w = x' + e w + e b := by abel
        rw [← hc, ← hc2] at this
        linarith
      · have hbd : b < d := lt_of_not_ge hdb
        have h2 : T2 P v (x' + e b + e w + e d) = v (x' + e w + e d) + P.r b := by
          rw [show x' + e b + e w + e d = x' + e w + e d + e b by abel]
          exact ex _ _ (gadd _ _ _ (gadd _ _ _ hx' (hbd.le.trans (hdl.trans (hlq.trans hqw))))
            hbd.le)
        have h3 : T2 P v (x' + e b + e q + e d) ≤ v (x' + e q + e d) + P.r b := by
          rw [show x' + e b + e q + e d = x' + e q + e d + e b by abel]; exact up _ _
        have := A4 x' d l q w hdl hlq hqw
        linarith
  · -- (A.5)
    intro x l q hlq
    rw [remanT2_A5form]
    rcases remanT2_decomp x with rfl | ⟨b, x', rfl, hx'⟩
    · -- x = 0
      have H := remanT2_wsum P.p hp (fun i => T2 P v (0 + e q + e (max i l)))
        (fun i => T2 P v (0 + e (max i l))) (fun _ => P.r q - P.cL) (fun i => by
          try dsimp only
          by_cases hM : max i l ≤ q
          · have h1 := ex (0 + e q) (max i l)
              (gadd _ _ _ (remanT2_ge_zero _) hM)
            have h2 := up 0 (max i l)
            have := A1 0 q
            linarith
          · have hqM : q < max i l := lt_of_not_ge hM
            have h1 : T2 P v (0 + e q + e (max i l)) = v (0 + e (max i l)) + P.r q := by
              rw [show (0 : Fin K → ℕ) + e q + e (max i l) = 0 + e (max i l) + e q by abel]
              exact ex _ _ (gadd _ _ _ (remanT2_ge_zero _) hqM.le)
            have h2 := upL (0 + e (max i l))
            linarith)
      rw [hconst] at H
      have h1 := up 0 q
      have h2 := remanT2_zero P v
      linarith
    · by_cases hbl : b ≤ l
      · -- Case I
        have H := remanT2_wsum P.p hp (fun i => T2 P v (x' + e b + e q + e (max i l)))
          (fun i => T2 P v (x' + e b + e (max i l)))
          (fun i => v (x' + e q + e (max i l)) - v (x' + e (max i l))) (fun i => by
            try dsimp only
            have hbM : b ≤ max i l := hbl.trans (le_max_right _ _)
            have h1 : T2 P v (x' + e b + e q + e (max i l)) = v (x' + e q + e (max i l)) + P.r b := by
              rw [show x' + e b + e q + e (max i l) = x' + e q + e (max i l) + e b by abel]
              exact ex _ _ (gadd _ _ _ (gadd _ _ _ hx' (hbl.trans hlq)) hbM)
            have h2 : T2 P v (x' + e b + e (max i l)) ≤ v (x' + e (max i l)) + P.r b := by
              rw [show x' + e b + e (max i l) = x' + e (max i l) + e b by abel]; exact up _ _
            linarith)
        simp only [mul_sub, Finset.sum_sub_distrib] at H
        have h1 : T2 P v (x' + e b + e q) ≤ v (x' + e q) + P.r b := by
          rw [show x' + e b + e q = x' + e q + e b by abel]; exact up _ _
        have h2 := ex x' b hx'
        have := A5' x' l q hlq
        linarith
      · have hlb : l < b := lt_of_not_ge hbl
        by_cases hbq : b ≤ q
        · -- Case B
          have H := remanT2_wsum P.p hp (fun i => T2 P v (x' + e b + e q + e (max i l)))
            (fun i => T2 P v (x' + e b + e (max i l)))
            (fun i => v (x' + e q + e (max i b)) - v (x' + e (max i b))) (fun i => by
              try dsimp only
              by_cases hib : i < b
              · have hM : max i l < b := max_lt hib hlb
                rw [max_eq_right hib.le]
                have h1 := ex (x' + e b + e q) (max i l)
                  (gadd _ _ _ (gadd _ _ _ (gmono _ _ _ hx' hM.le) hM.le) (hM.le.trans hbq))
                have h2 := up (x' + e b) (max i l)
                have hc : x' + e b + e q = x' + e q + e b := by abel
                rw [hc] at h1
                rw [hc]
                linarith
              · have hbi : b ≤ i := not_lt.1 hib
                rw [max_eq_left (hlb.le.trans hbi), max_eq_left hbi]
                have h1 : T2 P v (x' + e b + e q + e i) = v (x' + e q + e i) + P.r b := by
                  rw [show x' + e b + e q + e i = x' + e q + e i + e b by abel]
                  exact ex _ _ (gadd _ _ _ (gadd _ _ _ hx' hbq) hbi)
                have h2 : T2 P v (x' + e b + e i) ≤ v (x' + e i) + P.r b := by
                  rw [show x' + e b + e i = x' + e i + e b by abel]; exact up _ _
                linarith)
          simp only [mul_sub, Finset.sum_sub_distrib] at H
          have h1 : T2 P v (x' + e b + e q) ≤ v (x' + e q) + P.r b := by
            rw [show x' + e b + e q = x' + e q + e b by abel]; exact up _ _
          have h2 := ex x' b hx'
          have := A5' x' b q hbq
          linarith
        · -- Case A
          have hqb : q < b := lt_of_not_ge hbq
          have H := remanT2_wsum P.p hp (fun i => T2 P v (x' + e b + e q + e (max i l)))
            (fun i => T2 P v (x' + e b + e (max i l)))
            (fun i => (v (x' + e b + e (max i q)) - v (x' + e (max i q))) + (P.r q - P.r b))
            (fun i => by
              try dsimp only
              by_cases hiq : i ≤ q
              · have hM : max i l ≤ q := max_le hiq hlq
                rw [max_eq_right hiq]
                have h1 := ex (x' + e b + e q) (max i l)
                  (gadd _ _ _ (gadd _ _ _ (gmono _ _ _ hx' (hM.trans hqb.le)) (hM.trans hqb.le)) hM)
                have h2 := up (x' + e b) (max i l)
                have := A2 x' q b hqb
                have hc : x' + e b + e q = x' + e q + e b := by abel
                rw [hc]
                rw [hc] at h1
                linarith
              · have hqi : q < i := lt_of_not_ge hiq
                rw [max_eq_left (hlq.trans hqi.le), max_eq_left hqi.le]
                have h1 : T2 P v (x' + e b + e q + e i) = v (x' + e b + e i) + P.r q := by
                  rw [show x' + e b + e q + e i = x' + e b + e i + e q by abel]
                  exact ex _ _ (gadd _ _ _ (gadd _ _ _ (gmono _ _ _ hx' hqb.le) hqb.le) hqi.le)
                have h2 : T2 P v (x' + e b + e i) ≤ v (x' + e i) + P.r b := by
                  rw [show x' + e b + e i = x' + e i + e b by abel]; exact up _ _
                linarith)
          simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hconst] at H
          have h1 := up (x' + e b) q
          have h2 := ex x' b hx'
          have := A5' x' q b hqb.le
          linarith
  · -- (A.6)
    intro x l q w hlq hqw
    rw [remanT2_A6form]
    rcases remanT2_decompC x w with hx | ⟨b, x', rfl, hx', hbw⟩
    · have H := remanT2_wsum P.p hp (fun i => T2 P v (x + e q + e (max i l)))
        (fun i => T2 P v (x + e w + e (max i l))) (fun _ => P.r q - P.r w) (fun i => by
          try dsimp only
          by_cases hM : max i l ≤ q
          · have h1 := ex (x + e q) (max i l) (gadd _ _ _ (gmono _ _ _ hx (hM.trans hqw.le)) hM)
            have h2 := up (x + e w) (max i l)
            have := A2 x q w hqw
            linarith
          · have hqM : q < max i l := lt_of_not_ge hM
            have h1 : T2 P v (x + e q + e (max i l)) = v (x + e (max i l)) + P.r q := by
              rw [show x + e q + e (max i l) = x + e (max i l) + e q by abel]
              exact ex _ _ (gadd _ _ _ (gmono _ _ _ hx hqw.le) hqM.le)
            have h2 : T2 P v (x + e w + e (max i l)) ≤ v (x + e (max i l)) + P.r w := by
              rw [show x + e w + e (max i l) = x + e (max i l) + e w by abel]; exact up _ _
            linarith)
      rw [hconst] at H
      have h1 := up x q
      have h2 := ex x w hx
      linarith
    · have h2w : T2 P v (x' + e b + e w) = v (x' + e w) + P.r b := by
        rw [show x' + e b + e w = x' + e w + e b by abel]
        exact ex _ _ (gadd _ _ _ hx' hbw.le)
      by_cases hbl : b ≤ l
      · -- Case I
        have H := remanT2_wsum P.p hp (fun i => T2 P v (x' + e b + e q + e (max i l)))
          (fun i => T2 P v (x' + e b + e w + e (max i l)))
          (fun i => v (x' + e q + e (max i l)) - v (x' + e w + e (max i l))) (fun i => by
            try dsimp only
            have hbM : b ≤ max i l := hbl.trans (le_max_right _ _)
            have h1 : T2 P v (x' + e b + e q + e (max i l)) = v (x' + e q + e (max i l)) + P.r b := by
              rw [show x' + e b + e q + e (max i l) = x' + e q + e (max i l) + e b by abel]
              exact ex _ _ (gadd _ _ _ (gadd _ _ _ hx' (hbl.trans hlq)) hbM)
            have h2 : T2 P v (x' + e b + e w + e (max i l)) ≤ v (x' + e w + e (max i l)) + P.r b := by
              rw [show x' + e b + e w + e (max i l) = x' + e w + e (max i l) + e b by abel]
              exact up _ _
            linarith)
        simp only [mul_sub, Finset.sum_sub_distrib] at H
        have h1 : T2 P v (x' + e b + e q) ≤ v (x' + e q) + P.r b := by
          rw [show x' + e b + e q = x' + e q + e b by abel]; exact up _ _
        have := A6' x' l q w hlq hqw
        linarith
      · have hlb : l < b := lt_of_not_ge hbl
        by_cases hbq : b ≤ q
        · -- Case B
          have H := remanT2_wsum P.p hp (fun i => T2 P v (x' + e b + e q + e (max i l)))
            (fun i => T2 P v (x' + e b + e w + e (max i l)))
            (fun i => v (x' + e q + e (max i b)) - v (x' + e w + e (max i b))) (fun i => by
              try dsimp only
              by_cases hib : i < b
              · have hM : max i l < b := max_lt hib hlb
                rw [max_eq_right hib.le]
                have h1 := ex (x' + e b + e q) (max i l)
                  (gadd _ _ _ (gadd _ _ _ (gmono _ _ _ hx' hM.le) hM.le) (hM.le.trans hbq))
                have h2 := up (x' + e b + e w) (max i l)
                have hc : x' + e b + e q = x' + e q + e b := by abel
                have hc2 : x' + e b + e w = x' + e w + e b := by abel
                rw [hc] at h1
                rw [hc2] at h2
                rw [hc, hc2]
                linarith
              · have hbi : b ≤ i := not_lt.1 hib
                rw [max_eq_left (hlb.le.trans hbi), max_eq_left hbi]
                have h1 : T2 P v (x' + e b + e q + e i) = v (x' + e q + e i) + P.r b := by
                  rw [show x' + e b + e q + e i = x' + e q + e i + e b by abel]
                  exact ex _ _ (gadd _ _ _ (gadd _ _ _ hx' hbq) hbi)
                have h2 : T2 P v (x' + e b + e w + e i) ≤ v (x' + e w + e i) + P.r b := by
                  rw [show x' + e b + e w + e i = x' + e w + e i + e b by abel]; exact up _ _
                linarith)
          simp only [mul_sub, Finset.sum_sub_distrib] at H
          have h1 : T2 P v (x' + e b + e q) ≤ v (x' + e q) + P.r b := by
            rw [show x' + e b + e q = x' + e q + e b by abel]; exact up _ _
          have := A6' x' b q w hbq hqw
          linarith
        · -- Case A (q < b < w)
          have hqb : q < b := lt_of_not_ge hbq
          have H := remanT2_wsum P.p hp (fun i => T2 P v (x' + e b + e q + e (max i l)))
            (fun i => T2 P v (x' + e b + e w + e (max i l)))
            (fun i => (v (x' + e b + e (max i q)) - v (x' + e w + e (max i q))) + (P.r q - P.r b))
            (fun i => by
              try dsimp only
              by_cases hiq : i ≤ q
              · have hM : max i l ≤ q := max_le hiq hlq
                rw [max_eq_right hiq]
                have h1 := ex (x' + e b + e q) (max i l)
                  (gadd _ _ _ (gadd _ _ _ (gmono _ _ _ hx' (hM.trans hqb.le)) (hM.trans hqb.le)) hM)
                have h2 := up (x' + e b + e w) (max i l)
                have := A2 (x' + e w) q b hqb
                have hc : x' + e b + e q = x' + e q + e b := by abel
                have hc2 : x' + e b + e w = x' + e w + e b := by abel
                have hc3 : x' + e w + e q = x' + e q + e w := by abel
                rw [hc] at h1
                rw [hc2] at h2
                rw [hc3] at this
                rw [hc, hc2, hc3]
                linarith
              · have hqi : q < i := lt_of_not_ge hiq
                rw [max_eq_left (hlq.trans hqi.le), max_eq_left hqi.le]
                have h1 : T2 P v (x' + e b + e q + e i) = v (x' + e b + e i) + P.r q := by
                  rw [show x' + e b + e q + e i = x' + e b + e i + e q by abel]
                  exact ex _ _ (gadd _ _ _ (gadd _ _ _ (gmono _ _ _ hx' hqb.le) hqb.le) hqi.le)
                have h2 : T2 P v (x' + e b + e w + e i) ≤ v (x' + e w + e i) + P.r b := by
                  rw [show x' + e b + e w + e i = x' + e w + e i + e b by abel]; exact up _ _
                linarith)
          simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hconst] at H
          have h1 := up (x' + e b) q
          have := A6' x' q b w hqb.le hbw
          linarith


theorem solution {K : ℕ} (P : Params K) (hP : Standing P) (v : (Fin K → ℕ) → ℝ) (hv : VA P v) : VA P (T P v) := by
  have h1 := remanT1_VA P hP v hv
  have h2 := remanT2_VA P hP v hv
  obtain ⟨-, -, hpsum, hrm, -, hha, hh0, hrc, -, hα, -, hμ, hlam, hsum⟩ := hP
  set g1 := T1 P v
  set g2 := T2 P v
  have hT : ∀ y, T P v y = P.μ * g1 y + P.lam * g2 y + hold P y := fun y => rfl
  have hold_add : ∀ (y : Fin K → ℕ) (a : Fin K), hold P (y + e a) = hold P y + P.h a := by
    intro y a
    unfold hold
    simp [e, Pi.single_apply, mul_add, Finset.sum_add_distrib]
  have hpart : ∀ l : Fin K, (∑ i ∈ Finset.univ.filter (· ≤ l), P.p i)
      + (∑ i ∈ Finset.univ.filter (l < ·), P.p i) = 1 := by
    intro l
    rw [← hpsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ l)]
    congr 1
    apply Finset.sum_congr
    · ext i; simp [not_le]
    · intro i _; rfl
  have hsplit : ∀ (s : Finset (Fin K)) (y : Fin K → (Fin K → ℕ)),
      ∑ i ∈ s, P.p i * T P v (y i) = P.μ * ∑ i ∈ s, P.p i * g1 (y i)
        + P.lam * ∑ i ∈ s, P.p i * g2 (y i) + ∑ i ∈ s, P.p i * hold P (y i) := by
    intro s y
    simp only [hT, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  have hshift : ∀ (s : Finset (Fin K)) (y : Fin K → (Fin K → ℕ)) (a : Fin K),
      ∑ i ∈ s, P.p i * hold P (y i + e a) = ∑ i ∈ s, P.p i * hold P (y i)
        + P.h a * ∑ i ∈ s, P.p i := by
    intro s y a
    simp only [hold_add, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro i _; ring
  obtain ⟨g1A1, g1A2, g1A3, g1A4, g1A5, g1A6⟩ := h1
  obtain ⟨g2A1, g2A2, g2A3, g2A4, g2A5, g2A6⟩ := h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x w
    have a := g1A1 x w; have b := g2A1 x w
    rw [hT, hT, hold_add]
    have := mul_le_mul_of_nonneg_left a hμ.le
    have := mul_le_mul_of_nonneg_left b hlam.le
    have := mul_nonneg hα.le (sub_nonneg.2 (hrc w).le)
    have := hh0 w
    have e1 : P.cL - P.r w = P.α * (P.cL - P.r w) + P.lam * (P.cL - P.r w) + P.μ * (P.cL - P.r w) := by
      linear_combination (-(P.cL - P.r w)) * hsum
    nlinarith
  · intro x q w hqw
    have a := g1A2 x q w hqw; have b := g2A2 x q w hqw
    rw [hT, hT, hold_add, hold_add]
    have := mul_le_mul_of_nonneg_left a hμ.le
    have := mul_le_mul_of_nonneg_left b hlam.le
    have := mul_nonneg hα.le (sub_nonneg.2 (hrm hqw.le))
    have := hha hqw.le
    have e1 : P.r w - P.r q = P.α * (P.r w - P.r q) + P.lam * (P.r w - P.r q) + P.μ * (P.r w - P.r q) := by
      linear_combination (-(P.r w - P.r q)) * hsum
    nlinarith
  · intro x d l q _ _ 
    have a := g1A3 x d l q ‹_› ‹_›; have b := g2A3 x d l q ‹_› ‹_›
    simp only [hT, hold_add]
    nlinarith [mul_le_mul_of_nonneg_left a hμ.le, mul_le_mul_of_nonneg_left b hlam.le]
  · intro x d l q w _ _ _
    have a := g1A4 x d l q w ‹_› ‹_› ‹_›; have b := g2A4 x d l q w ‹_› ‹_› ‹_›
    simp only [hT, hold_add]
    nlinarith [mul_le_mul_of_nonneg_left a hμ.le, mul_le_mul_of_nonneg_left b hlam.le]
  · intro x l q hlq
    have a := g1A5 x l q hlq; have b := g2A5 x l q hlq
    rw [hsplit, hsplit, hsplit, hsplit]
    simp only [hT, hold_add, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [← Finset.sum_mul] at a b
    have hp := hpart l
    have k : ∀ c : ℝ, (∑ i ∈ Finset.univ.filter (· ≤ l), P.p i) * c
        + (∑ i ∈ Finset.univ.filter (l < ·), P.p i) * c = c := fun c => by rw [← add_mul, hp, one_mul]
    have k1 := k (hold P x); have k2 := k (P.h q); have k3 := k (P.h l)
    nlinarith [mul_le_mul_of_nonneg_left a hμ.le, mul_le_mul_of_nonneg_left b hlam.le]
  · intro x l q w hlq hqw
    have a := g1A6 x l q w hlq hqw; have b := g2A6 x l q w hlq hqw
    rw [hsplit, hsplit, hsplit, hsplit]
    simp only [hT, hold_add, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [← Finset.sum_mul] at a b
    have hp := hpart l
    have k : ∀ c : ℝ, (∑ i ∈ Finset.univ.filter (· ≤ l), P.p i) * c
        + (∑ i ∈ Finset.univ.filter (l < ·), P.p i) * c = c := fun c => by rw [← add_mul, hp, one_mul]
    have k1 := k (hold P x); have k2 := k (P.h q); have k3 := k (P.h l); have k4 := k (P.h w)
    nlinarith [mul_le_mul_of_nonneg_left a hμ.le, mul_le_mul_of_nonneg_left b hlam.le]
