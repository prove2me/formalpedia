-- Prove2me | solution 1 for ReliableFacilityLoc.Supermod.closed_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:56:22.167125+00:00
-- url     : https://prove2.me/submissions/aec4c5f6-97b0-42b4-b8df-2b936c83c11d

import Mathlib
import Definitions.Def_ReliableFacilityLoc_Supermod_RSP
import Definitions.Def_ReliableFacilityLoc_Supermod_ClosedForm

open Finset


namespace RFL3Aux
open ReliableFacilityLoc.Supermod

variable {J : ℕ}

noncomputable def hv (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) : List (Fin J) → ℝ
  | [] => phi
  | x :: xs => if d x ≤ phi then (1 - q x) * d x + q x * hv d phi q xs else phi

noncomputable def fv (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) : List (Fin J) → ℝ
  | [] => phi
  | x :: xs => (1 - q x) * d x + q x * fv d phi q xs

section
variable (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)

lemma hv_le (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) : ∀ L : List (Fin J), hv d phi q L ≤ phi
  | [] => le_rfl
  | x :: xs => by
    simp only [hv]
    split_ifs with h
    · have h1 : (1 - q x) * d x ≤ (1 - q x) * phi :=
        mul_le_mul_of_nonneg_left h (by linarith [hq1 x])
      have h2 := mul_le_mul_of_nonneg_left (hv_le hq0 hq1 xs) (hq0 x)
      nlinarith
    · exact le_rfl

lemma hv_all_gt : ∀ L : List (Fin J), (∀ y ∈ L, phi < d y) → hv d phi q L = phi
  | [] => fun _ => rfl
  | x :: xs => fun h => by
    simp only [hv]
    rw [if_neg (not_le.mpr (h x (by simp)))]

lemma hv_erase (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) : ∀ (L : List (Fin J)),
    L.Pairwise (fun a b => d a ≤ d b) → ∀ a ∈ L,
    hv d phi q L ≤ (1 - q a) * d a + q a * hv d phi q (L.erase a)
  | [], _, a, ha => absurd ha List.not_mem_nil
  | y :: ys, hs, a, ha => by
    rw [List.pairwise_cons] at hs
    by_cases hya : y = a
    · subst hya
      rw [List.erase_cons_head]
      simp only [hv]
      split_ifs with h
      · exact le_rfl
      · have hall : ∀ z ∈ ys, phi < d z := fun z hz => lt_of_lt_of_le (not_le.mp h) (hs.1 z hz)
        rw [hv_all_gt d phi q ys hall]
        have := hq1 y
        nlinarith [not_le.mp h]
    · have ha' : a ∈ ys := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hya
        · exact h
      rw [List.erase_cons_tail (by simpa using hya)]
      have hya' : d y ≤ d a := hs.1 a ha'
      simp only [hv]
      split_ifs with h
      · have ih := hv_erase hq0 hq1 ys hs.2 a ha'
        have h1 := mul_le_mul_of_nonneg_left ih (hq0 y)
        have h2 : 0 ≤ (1 - q a) * (1 - q y) * (d a - d y) := by
          apply mul_nonneg (mul_nonneg _ _) <;> linarith [hq1 a, hq1 y]
        nlinarith
      · have := hq1 a
        have : phi < d a := lt_of_lt_of_le (not_le.mp h) hya'
        nlinarith

lemma hv_eq_fv : ∀ L : List (Fin J),
    hv d phi q L = fv d phi q (L.takeWhile (fun j => decide (d j ≤ phi)))
  | [] => rfl
  | x :: xs => by
    rw [List.takeWhile_cons]
    by_cases h : d x ≤ phi
    · simp only [h, decide_true, if_true, hv, fv, hv_eq_fv xs]
    · simp [h, hv, fv]

lemma prodQ_zero (L : List (Fin J)) : prodQ q L 0 = 1 := by simp [prodQ]

lemma prodQ_cons_succ (x : Fin J) (L : List (Fin J)) (k : ℕ) :
    prodQ q (x :: L) (k + 1) = q x * prodQ q L k := by simp [prodQ]

lemma prodQ_succ (L : List (Fin J)) (n : ℕ) (hn : n < L.length) :
    prodQ q L (n + 1) = prodQ q L n * q L[n] := by
  unfold prodQ
  rw [List.take_add_one, List.getElem?_eq_getElem hn, List.map_append, List.prod_append]
  simp

lemma prod_map_mem01 (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) :
    ∀ l : List (Fin J), 0 ≤ (l.map q).prod ∧ (l.map q).prod ≤ 1
  | [] => by simp
  | x :: xs => by
    obtain ⟨h1, h2⟩ := prod_map_mem01 hq0 hq1 xs
    simp only [List.map_cons, List.prod_cons]
    exact ⟨mul_nonneg (hq0 x) h1, mul_le_one₀ (hq1 x).le h1 h2⟩

lemma prodQ_mem01 (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (L : List (Fin J)) (n : ℕ) :
    0 ≤ prodQ q L n ∧ prodQ q L n ≤ 1 := prod_map_mem01 q hq0 hq1 _

lemma sum_Icc_shift (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 (n + 1), f k = ∑ i ∈ range (n + 1), f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ _ (n + 1)]

lemma Ck_cons_one (x : Fin J) (xs : List (Fin J)) (h : d x ≤ phi) :
    Ck d phi q (x :: xs) 1 = (1 - q x) * d x := by
  have hc : countLE d phi (x :: xs) = countLE d phi xs + 1 := by
    unfold countLE; exact List.countP_cons_of_pos (by simpa using h)
  unfold Ck
  rw [hc, if_neg (by omega), if_pos (by omega)]
  simp [prodQ_zero]

lemma Ck_cons_succ (x : Fin J) (xs : List (Fin J)) (h : d x ≤ phi) (k : ℕ) (hk : 1 ≤ k) :
    Ck d phi q (x :: xs) (k + 1) = q x * Ck d phi q xs k := by
  have hc : countLE d phi (x :: xs) = countLE d phi xs + 1 := by
    unfold countLE; exact List.countP_cons_of_pos (by simpa using h)
  unfold Ck
  rw [hc]
  by_cases h1 : k = countLE d phi xs + 1
  · rw [if_pos (by omega), if_pos h1, prodQ_cons_succ]; ring
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : 1 ≤ k ∧ k ≤ countLE d phi xs
    · rw [if_pos (by omega), if_pos h2]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, prodQ_cons_succ, List.map_cons]
      simp [List.getD_cons_succ]
      ring
    · rw [if_neg (by omega), if_neg h2, mul_zero]

lemma sumCk_eq : ∀ L : List (Fin J), L.Pairwise (fun a b => d a ≤ d b) →
    ∑ k ∈ Icc 1 (countLE d phi L + 1), Ck d phi q L k = hv d phi q L
  | [], _ => by
    simp [countLE, Ck, prodQ, hv]
  | x :: xs, hs => by
    rw [List.pairwise_cons] at hs
    by_cases h : d x ≤ phi
    · have hc : countLE d phi (x :: xs) = countLE d phi xs + 1 := by
        unfold countLE; exact List.countP_cons_of_pos (by simpa using h)
      rw [hc, sum_Icc_shift, sum_range_succ']
      simp only [hv, if_pos h]
      rw [Ck_cons_one d phi q x xs h]
      have : ∀ i ∈ range (countLE d phi xs + 1), Ck d phi q (x :: xs) (i + 1 + 1) =
          q x * Ck d phi q xs (i + 1) := fun i _ => Ck_cons_succ d phi q x xs h (i + 1) (by omega)
      rw [sum_congr rfl this, ← mul_sum, ← sum_Icc_shift, sumCk_eq xs hs.2]
      ring
    · have hall : ∀ z ∈ x :: xs, phi < d z := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact not_le.mp h
        · exact lt_of_lt_of_le (not_le.mp h) (hs.1 z hz)
      have hc : countLE d phi (x :: xs) = 0 := by
        unfold countLE
        rw [List.countP_eq_zero]
        intro a ha; simpa using hall a ha
      rw [hc, hv_all_gt d phi q _ hall]
      simp [Ck, hc, prodQ_zero]

lemma fv_sum : ∀ M : List (Fin J),
    fv d phi q M = ∑ n ∈ range M.length, prodQ q M n * (M.map (fun j => (1 - q j) * d j)).getD n 0
      + prodQ q M M.length * phi
  | [] => by simp [fv, prodQ]
  | x :: xs => by
    rw [List.length_cons, sum_range_succ', fv, fv_sum xs]
    simp only [prodQ_cons_succ, prodQ_zero, List.map_cons, List.getD_cons_succ,
      List.getD_cons_zero]
    rw [mul_add, mul_sum]
    have : ∀ i ∈ range xs.length, q x * (prodQ q xs i *
        (List.map (fun j => (1 - q j) * d j) xs).getD i 0) =
        q x * prodQ q xs i * (List.map (fun j => (1 - q j) * d j) xs).getD i 0 :=
      fun i _ => by ring
    rw [sum_congr rfl this]
    ring

end
end RFL3Aux



namespace RFL3Aux
open ReliableFacilityLoc.Supermod

variable {J : ℕ}

lemma exists_unique_one {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hb : ∀ i, f i = 0 ∨ f i = 1) (hs : ∑ i, f i = 1) :
    ∃ a, f a = 1 ∧ ∀ k, k ≠ a → f k = 0 := by
  have hnn : ∀ i, 0 ≤ f i := fun i => by rcases hb i with h | h <;> rw [h] <;> norm_num
  by_contra hne
  push_neg at hne
  have : ∀ i, f i = 0 := by
    intro i
    rcases hb i with h | h
    · exact h
    · obtain ⟨k, hk, hk0⟩ := hne i h
      have h2 : f i + f k ≤ ∑ j, f j := by
        rw [← sum_pair hk.symm]
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => hnn j)
      rcases hb k with h' | h'
      · exact absurd h' hk0
      · linarith
  simp [this] at hs

lemma nonneg_of_bin {x : ℝ} (h : x = 0 ∨ x = 1) : 0 ≤ x := by
  rcases h with h | h <;> rw [h] <;> norm_num

lemma lower_core (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (R : ℕ) (S : Finset (Fin J))
    (L : List (Fin J)) (hLsort : L.Pairwise (fun a b => d a ≤ d b)) (hSL : ∀ j ∈ S, j ∈ L)
    (Yr : Fin J → ℕ → ℝ) (Ye : ℕ → ℝ) (π : ℕ → ℝ)
    (hbR : ∀ k n, Yr k n = 0 ∨ Yr k n = 1) (hbE : ∀ n, Ye n = 0 ∨ Ye n = 1)
    (hlevel : ∀ n ≤ R, ∑ k, Yr k n + Ye n + ∑ s ∈ range n, Ye s = 1)
    (hreg : ∀ k, ∑ n ∈ range R, Yr k n ≤ 1)
    (hem : ∑ n ∈ range (R + 1), Ye n = 1)
    (hout : ∀ k, k ∉ S → ∑ n ∈ range R, Yr k n = 0)
    (hπ0 : π 0 = 1) (hπs : ∀ n < R, π (n + 1) = π n * ∑ k, q k * Yr k n) :
    hv d phi q L ≤ ∑ n ∈ range (R + 1),
      π n * (∑ k, (1 - q k) * d k * Yr k n + phi * Ye n) := by
  set c : ℕ → ℝ := fun n => ∑ k, (1 - q k) * d k * Yr k n + phi * Ye n with hc
  set A : ℕ → ℝ := fun n => ∑ i ∈ range n, π i * c i with hA
  have hRnn : ∀ k n, 0 ≤ Yr k n := fun k n => nonneg_of_bin (hbR k n)
  have hEnn : ∀ n, 0 ≤ Ye n := fun n => nonneg_of_bin (hbE n)
  have key : ∀ n, n ≤ R + 1 →
      ((∃ s < n, Ye s = 1) ∧ hv d phi q L ≤ A n) ∨
      ((∀ s < n, Ye s = 0) ∧ n ≤ R ∧ 0 ≤ π n ∧ ∃ M : List (Fin J),
        M.Pairwise (fun a b => d a ≤ d b) ∧
        (∀ j ∈ S, (∀ s < n, Yr j s = 0) → j ∈ M) ∧
        hv d phi q L ≤ A n + π n * hv d phi q M) := by
    intro n
    induction n with
    | zero =>
      intro _
      right
      refine ⟨fun s hs => absurd hs (Nat.not_lt_zero _), Nat.zero_le _, by rw [hπ0]; norm_num,
        L, hLsort, fun j hj _ => hSL j hj, ?_⟩
      simp [hA, hπ0]
    | succ n ih =>
      intro hn
      have hAs : A (n + 1) = A n + π n * c n := by simp only [hA]; rw [sum_range_succ]
      rcases ih (by omega) with ⟨⟨s, hs, hYs⟩, hle⟩ | ⟨hnot, hnR, hπn, M, hMs, hMmem, hle⟩
      · -- emergency already used
        left
        refine ⟨⟨s, by omega, hYs⟩, ?_⟩
        have hlev := hlevel n (by omega)
        have hge : 1 ≤ ∑ s ∈ range n, Ye s := by
          rw [← hYs]
          exact single_le_sum (fun i _ => hEnn i) (mem_range.mpr hs)
        have hsum0 : ∑ k, Yr k n + Ye n ≤ 0 := by linarith
        have hk0 : ∀ k, Yr k n = 0 := by
          intro k
          have h1 : Yr k n ≤ ∑ k, Yr k n := single_le_sum (fun i _ => hRnn i n) (mem_univ k)
          have := hRnn k n
          have := hEnn n
          have : 0 ≤ ∑ k, Yr k n := sum_nonneg (fun i _ => hRnn i n)
          linarith
        have he0 : Ye n = 0 := by
          have : 0 ≤ ∑ k, Yr k n := sum_nonneg (fun i _ => hRnn i n)
          linarith [hEnn n]
        have hc0 : c n = 0 := by simp [hc, hk0, he0]
        rw [hAs, hc0]; simpa using hle
      · have hlev := hlevel n hnR
        have hsum0 : ∑ s ∈ range n, Ye s = 0 :=
          sum_eq_zero (fun s hs => hnot s (mem_range.mp hs))
        rw [hsum0, add_zero] at hlev
        rcases hbE n with he | he
        · -- regular facility at level n
          rw [he, add_zero] at hlev
          obtain ⟨a, ha1, ha0⟩ := exists_unique_one (fun k => Yr k n) (fun k => hbR k n) hlev
          have hnR' : n < R := by
            rcases Nat.lt_or_ge n R with h | h
            · exact h
            · exfalso
              have hnR'' : n = R := le_antisymm hnR h
              rw [sum_range_succ, sum_eq_zero (fun s hs => hnot s (by
                rw [mem_range] at hs; omega)), ← hnR'', he] at hem
              norm_num at hem
          have haS : a ∈ S := by
            by_contra haS
            have h0 := hout a haS
            have : Yr a n ≤ ∑ n ∈ range R, Yr a n :=
              single_le_sum (fun i _ => hRnn a i) (mem_range.mpr hnR')
            linarith
          have hprev : ∀ s < n, Yr a s = 0 := by
            intro s hs
            rcases hbR a s with h | h
            · exact h
            · exfalso
              have h2 : Yr a s + Yr a n ≤ ∑ n ∈ range R, Yr a n := by
                rw [← sum_pair (show s ≠ n by omega)]
                apply sum_le_sum_of_subset_of_nonneg
                · intro x hx
                  simp only [mem_insert, mem_singleton] at hx
                  rcases hx with rfl | rfl <;> rw [mem_range] <;> omega
                · intro i _ _; exact hRnn a i
              have := hreg a
              linarith
          have haM : a ∈ M := hMmem a haS hprev
          have hcn : c n = (1 - q a) * d a := by
            simp only [hc, he, mul_zero, add_zero]
            rw [sum_eq_single a (fun k _ hk => by simp [ha0 k hk]) (by simp)]
            rw [ha1, mul_one]
          have hπn1 : π (n + 1) = π n * q a := by
            rw [hπs n hnR', sum_eq_single a (fun k _ hk => by simp [ha0 k hk]) (by simp)]
            rw [ha1, mul_one]
          right
          refine ⟨fun s hs => ?_, by omega, ?_, M.erase a, hMs.sublist (List.erase_sublist),
            ?_, ?_⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
            · exact hnot s h
            · rw [h]; exact he
          · rw [hπn1]; exact mul_nonneg hπn (hq0 a)
          · intro j hj hjs
            have hja : j ≠ a := by
              rintro rfl
              have := hjs n (by omega)
              linarith
            exact (List.mem_erase_of_ne hja).mpr (hMmem j hj (fun s hs => hjs s (by omega)))
          · rw [hAs, hcn, hπn1]
            have hk := hv_erase d phi q hq0 hq1 M hMs a haM
            have := mul_le_mul_of_nonneg_left hk hπn
            nlinarith
        · -- emergency at level n
          rw [he] at hlev
          have hk0 : ∀ k, Yr k n = 0 := by
            intro k
            have h1 : Yr k n ≤ ∑ k, Yr k n := single_le_sum (fun i _ => hRnn i n) (mem_univ k)
            have := hRnn k n
            linarith
          have hcn : c n = phi := by simp [hc, hk0, he]
          left
          refine ⟨⟨n, by omega, he⟩, ?_⟩
          rw [hAs, hcn]
          have := mul_le_mul_of_nonneg_left (hv_le d phi q hq0 hq1 M) hπn
          linarith
  rcases key (R + 1) le_rfl with ⟨_, h⟩ | ⟨_, h, _⟩
  · exact h
  · omega

end RFL3Aux



namespace RFL3Aux
open ReliableFacilityLoc.Supermod

variable {J : ℕ}

@[simp] lemma qExt_last (q : Fin J → ℝ) : qExt q (Fin.last J) = 0 := by simp [qExt]
@[simp] lemma qExt_cs (q : Fin J → ℝ) (k : Fin J) : qExt q k.castSucc = q k := by simp [qExt]
@[simp] lemma dExt_last (d : Fin J → ℝ) (phi : ℝ) : dExt d phi (Fin.last J) = phi := by
  simp [dExt]
@[simp] lemma dExt_cs (d : Fin J → ℝ) (phi : ℝ) (k : Fin J) : dExt d phi k.castSucc = d k := by
  simp [dExt]

section
variable {q : Fin J → ℝ} {R : ℕ} {S : Finset (Fin J)} {Y P W : Fin (J + 1) → Fin (R + 1) → ℝ}

lemma P_eq (hfe : IsFeasible q R S Y P W) (j : Fin (J + 1)) (r : Fin (R + 1)) :
    P j r = (1 - qExt q j) * P (Fin.last J) r := by
  refine Fin.cases ?_ (fun r' => ?_) r
  · rw [hfe.prob_zero, hfe.prob_zero]; simp
  · rw [hfe.prob_succ, hfe.prob_succ]; simp

lemma W_eq (hfe : IsFeasible q R S Y P W) (j : Fin (J + 1)) (r : Fin (R + 1)) :
    W j r = P j r * Y j r := by
  have h1 := hfe.w_le_p j r
  have h2 := hfe.w_le_y j r
  have h3 := hfe.w_nonneg j r
  have h4 := hfe.w_ge j r
  rcases hfe.binary j r with h | h
  · rw [h] at h2 h4 ⊢; rw [mul_zero]; linarith
  · rw [h] at h2 h4 ⊢; rw [mul_one]; linarith
end

lemma lower (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (mu : Fin J → ℝ)
    (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (R : ℕ)
    (S : Finset (Fin J)) (L : List (Fin J)) (hLS : L.toFinset = S)
    (hLsort : L.Pairwise (fun a b => d a ≤ d b))
    (Y P W : Fin (J + 1) → Fin (R + 1) → ℝ) (hfe : IsFeasible q R S Y P W) :
    lam * hv d phi q L + ∑ j ∈ S, mu j ≤ objective lam d phi mu S W := by
  set Yr : Fin J → ℕ → ℝ := fun k n => if h : n < R + 1 then Y k.castSucc ⟨n, h⟩ else 0 with hYr
  set Ye : ℕ → ℝ := fun n => if h : n < R + 1 then Y (Fin.last J) ⟨n, h⟩ else 0 with hYe
  set π : ℕ → ℝ := fun n => if h : n < R + 1 then P (Fin.last J) ⟨n, h⟩ else 0 with hπ
  have eYr : ∀ k (r : Fin (R + 1)), Y k.castSucc r = Yr k r.val := by
    intro k r; simp only [hYr, dif_pos r.isLt]
  have eYe : ∀ (r : Fin (R + 1)), Y (Fin.last J) r = Ye r.val := by
    intro r; simp only [hYe, dif_pos r.isLt]
  have eπ : ∀ (r : Fin (R + 1)), P (Fin.last J) r = π r.val := by
    intro r; simp only [hπ, dif_pos r.isLt]
  have eW : ∀ j r, W j r = (1 - qExt q j) * π r.val * Y j r := by
    intro j r; rw [W_eq hfe, P_eq hfe, eπ]
  have hbR : ∀ k n, Yr k n = 0 ∨ Yr k n = 1 := by
    intro k n; simp only [hYr]; split_ifs with h
    · exact hfe.binary _ _
    · left; rfl
  have hbE : ∀ n, Ye n = 0 ∨ Ye n = 1 := by
    intro n; simp only [hYe]; split_ifs with h
    · exact hfe.binary _ _
    · left; rfl
  have hIio : ∀ r : Fin (R + 1), ∑ s ∈ Iio r, Y (Fin.last J) s = ∑ s ∈ range r.val, Ye s := by
    intro r
    rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, sum_map]
    apply sum_congr rfl; intro s _; rw [eYe]; rfl
  have hlevel : ∀ n ≤ R, ∑ k, Yr k n + Ye n + ∑ s ∈ range n, Ye s = 1 := by
    intro n hn
    have h := hfe.level_one ⟨n, by omega⟩
    rw [Fin.sum_univ_castSucc, hIio] at h
    simpa only [eYr, eYe] using h
  have hsumR : ∀ k : Fin J, ∑ r : Fin R, Y k.castSucc r.castSucc = ∑ n ∈ range R, Yr k n := by
    intro k
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl; intro r _; rw [eYr]; rfl
  have hreg : ∀ k, ∑ n ∈ range R, Yr k n ≤ 1 := fun k => by
    rw [← hsumR]; exact hfe.regular_once k
  have hem : ∑ n ∈ range (R + 1), Ye n = 1 := by
    rw [← Fin.sum_univ_eq_sum_range, ← hfe.emergency_once]
    apply sum_congr rfl; intro r _; rw [eYe]
  have hout : ∀ k, k ∉ S → ∑ n ∈ range R, Yr k n = 0 := fun k hk => by
    rw [← hsumR]; exact hfe.outside_S k hk
  have hπ0 : π 0 = 1 := by
    have := eπ 0
    simp only [Fin.val_zero] at this
    rw [← this, hfe.prob_zero]; simp
  have hπs : ∀ n < R, π (n + 1) = π n * ∑ k, q k * Yr k n := by
    intro n hn
    have e1 : π (n + 1) = P (Fin.last J) (Fin.succ ⟨n, hn⟩) := by
      rw [eπ]; rfl
    rw [e1, hfe.prob_succ]
    simp only [qExt_last, sub_zero, one_mul]
    rw [mul_sum]
    apply sum_congr rfl; intro k _
    rw [eW, eYr]
    simp only [qExt_cs, Fin.coe_castSucc]
    have : 1 - q k ≠ 0 := by linarith [hq1 k]
    field_simp
  have core := lower_core d phi q hq0 hq1 R S L hLsort
    (fun j hj => by rw [← hLS] at hj; simpa using hj) Yr Ye π hbR hbE hlevel hreg hem hout hπ0 hπs
  have hobj : objective lam d phi mu S W = lam * ∑ n ∈ range (R + 1),
      π n * (∑ k, (1 - q k) * d k * Yr k n + phi * Ye n) + ∑ j ∈ S, mu j := by
    unfold objective
    congr 1
    rw [sum_comm, ← Fin.sum_univ_eq_sum_range, mul_sum]
    apply sum_congr rfl; intro r _
    rw [Fin.sum_univ_castSucc]
    simp only [eW, eYr, eYe, qExt_cs, qExt_last, dExt_cs, dExt_last]
    have e : ∀ i, lam * d i * ((1 - q i) * π r * Yr i r) =
        lam * (π r * ((1 - q i) * d i * Yr i r)) := fun i => by ring
    rw [sum_congr rfl (fun i _ => e i), ← mul_sum, ← mul_sum]
    ring
  rw [hobj]
  have := mul_le_mul_of_nonneg_left core hlam
  linarith

end RFL3Aux



namespace RFL3Aux
open ReliableFacilityLoc.Supermod

variable {J : ℕ}

lemma sum_weight_getElem? (M : List (Fin J)) (g : Fin J → ℝ) (n : ℕ) :
    ∑ k, g k * (if M[n]? = some k then (1 : ℝ) else 0) = (M.map g).getD n 0 := by
  by_cases hn : n < M.length
  · rw [List.getElem?_eq_getElem hn, sum_eq_single M[n] (fun k _ hk => by simp [Ne.symm hk])
      (by simp)]
    simp [List.getD_eq_getElem?_getD, hn]
  · rw [List.getElem?_eq_none (by omega)]
    simp only [reduceCtorEq, if_false, mul_zero, sum_const_zero]
    rw [List.getD_eq_default _ _ (by simp; omega)]

lemma getD_map_mul (M : List (Fin J)) (c : ℝ) (g : Fin J → ℝ) (n : ℕ) :
    (M.map (fun i => c * g i)).getD n 0 = c * (M.map g).getD n 0 := by
  by_cases hn : n < M.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      mul_zero]

lemma upper (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (mu : Fin J → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (R : ℕ)
    (S : Finset (Fin J)) (hS : S.card ≤ R) (L : List (Fin J)) (hLnd : L.Nodup)
    (hLS : L.toFinset = S) :
    lam * hv d phi q L + ∑ j ∈ S, mu j ∈ feasibleValues lam d phi q mu R S := by
  set M := L.takeWhile (fun j => decide (d j ≤ phi)) with hM
  set m := M.length with hm
  have hMsub : M.Sublist L := List.takeWhile_sublist _
  have hmR : m ≤ R := by
    have h1 := hMsub.length_le
    have h2 := List.toFinset_card_of_nodup hLnd
    rw [hLS] at h2; omega
  have hMnd : M.Nodup := hLnd.sublist hMsub
  have hMS : ∀ k ∈ M, k ∈ S := fun k hk => by
    rw [← hLS, List.mem_toFinset]; exact hMsub.subset hk
  set πc : ℕ → ℝ := fun n => if n ≤ m then prodQ q M n else 0 with hπc
  set Y : Fin (J + 1) → Fin (R + 1) → ℝ := fun j r =>
    Fin.lastCases (if r.val = m then 1 else 0) (fun k => if M[r.val]? = some k then 1 else 0) j
    with hY
  set P : Fin (J + 1) → Fin (R + 1) → ℝ := fun j r => (1 - qExt q j) * πc r.val with hP
  set W : Fin (J + 1) → Fin (R + 1) → ℝ := fun j r => P j r * Y j r with hW
  have eYl : ∀ r, Y (Fin.last J) r = if r.val = m then 1 else 0 := fun r => by simp [hY]
  have eYc : ∀ (k : Fin J) r, Y k.castSucc r = if M[r.val]? = some k then 1 else 0 :=
    fun k r => by simp [hY]
  have hbin : ∀ j r, Y j r = 0 ∨ Y j r = 1 := by
    intro j r
    induction j using Fin.lastCases with
    | last => rw [eYl]; split_ifs <;> simp
    | cast k => rw [eYc]; split_ifs <;> simp
  have hπc01 : ∀ n, 0 ≤ πc n ∧ πc n ≤ 1 := by
    intro n; simp only [hπc]; split_ifs
    · exact prodQ_mem01 q hq0 hq1 M n
    · norm_num
  have hqE01 : ∀ j, 0 ≤ 1 - qExt q j ∧ 1 - qExt q j ≤ 1 := by
    intro j
    induction j using Fin.lastCases with
    | last => simp
    | cast k => simp only [qExt_cs]; constructor <;> linarith [hq0 k, hq1 k]
  have hP01 : ∀ j r, 0 ≤ P j r ∧ P j r ≤ 1 := by
    intro j r
    simp only [hP]
    obtain ⟨a1, a2⟩ := hqE01 j
    obtain ⟨b1, b2⟩ := hπc01 r.val
    exact ⟨mul_nonneg a1 b1, mul_le_one₀ a2 b1 b2⟩
  have hsumR : ∀ n, ∑ k : Fin J, (if M[n]? = some k then (1 : ℝ) else 0) =
      if n < m then 1 else 0 := by
    intro n
    have := sum_weight_getElem? M (fun _ => 1) n
    simp only [one_mul] at this
    rw [this]
    by_cases hn : n < m
    · have hn' : n < M.length := hn
      rw [if_pos hn]; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hn']
    · rw [if_neg hn, List.getD_eq_default _ _ (by simp; omega)]
  have hIio : ∀ r : Fin (R + 1), ∑ s ∈ Iio r, Y (Fin.last J) s =
      ∑ s ∈ range r.val, (if s = m then (1 : ℝ) else 0) := by
    intro r
    rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, sum_map]
    apply sum_congr rfl; intro s _; rw [eYl]; rfl
  have hfe : IsFeasible q R S Y P W := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hbin, ?_, ?_, ?_, ?_, ?_⟩
    · intro r
      rw [Fin.sum_univ_castSucc, hIio, eYl]
      simp only [eYc]
      rw [hsumR, sum_ite_eq' (range r.val) m (fun _ => (1 : ℝ))]
      simp only [mem_range]
      have := r.isLt
      split_ifs <;> (try norm_num) <;> omega
    · intro k
      simp only [eYc, Fin.coe_castSucc]
      rw [Fin.sum_univ_eq_sum_range (fun n => if M[n]? = some k then (1 : ℝ) else 0) R,
        sum_boole]
      have : ((range R).filter (fun n => M[n]? = some k)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [mem_filter] at ha hb
        obtain ⟨ha', hak⟩ := List.getElem?_eq_some_iff.mp ha.2
        obtain ⟨hb', hbk⟩ := List.getElem?_eq_some_iff.mp hb.2
        exact (hMnd.getElem_inj_iff).mp (hak.trans hbk.symm)
      exact_mod_cast this
    · simp only [eYl]
      rw [Fin.sum_univ_eq_sum_range (fun n => if n = m then (1 : ℝ) else 0) (R + 1),
        sum_ite_eq' (range (R + 1)) m (fun _ => (1 : ℝ)), if_pos (mem_range.mpr (by omega))]
    · intro j
      simp only [hP, Fin.val_zero, hπc, if_pos (Nat.zero_le _), prodQ_zero, mul_one]
    · intro j r
      simp only [hP, hW, Fin.val_succ, Fin.coe_castSucc]
      congr 1
      have e : ∀ k : Fin J, q k / (1 - q k) * ((1 - qExt q k.castSucc) * πc r.val *
          Y k.castSucc r.castSucc) = (q k * πc r.val) * (if M[r.val]? = some k then 1 else 0) := by
        intro k
        rw [eYc, qExt_cs, Fin.coe_castSucc]
        have : 1 - q k ≠ 0 := by linarith [hq1 k]
        field_simp
      rw [sum_congr rfl (fun k _ => e k), sum_weight_getElem?]
      by_cases hr : r.val < m
      · simp only [hπc, if_pos (show r.val + 1 ≤ m by omega), if_pos hr.le]
        have hr' : r.val < M.length := hr
        rw [prodQ_succ q M r.val hr, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hr']
        simp only [Option.map_some, Option.getD_some]
        ring
      · simp only [hπc, if_neg (show ¬ r.val + 1 ≤ m by omega)]
        rw [List.getD_eq_default _ _ (by simp; omega)]
    · intro j r
      simp only [hW]
      rcases hbin j r with h | h <;> rw [h] <;> simp [(hP01 j r).1]
    · intro j r
      simp only [hW]
      rcases hbin j r with h | h <;> rw [h] <;> simp [(hP01 j r).2]
    · intro j r
      simp only [hW]
      exact mul_nonneg (hP01 j r).1 (nonneg_of_bin (hbin j r))
    · intro j r
      simp only [hW]
      rcases hbin j r with h | h <;> rw [h] <;> simp [(hP01 j r).2]
    · intro j hj
      apply sum_eq_zero
      intro r _
      rw [eYc, if_neg]
      intro h
      exact hj (hMS j (List.mem_of_getElem? h))
  refine ⟨Y, P, W, hfe, ?_⟩
  -- objective value
  unfold objective
  congr 1
  rw [hv_eq_fv, ← hM, fv_sum, sum_comm]
  set G : ℕ → ℝ := fun n => πc n * ((M.map (fun j => (1 - q j) * d j)).getD n 0 +
    phi * if n = m then 1 else 0) with hG
  have hrow : ∀ r : Fin (R + 1), ∑ j, lam * dExt d phi j * W j r = lam * G r.val := by
    intro r
    rw [Fin.sum_univ_castSucc]
    simp only [hW, hP, eYc, eYl, qExt_cs, qExt_last, dExt_cs, dExt_last, hG]
    have e : ∀ i : Fin J, lam * d i * ((1 - q i) * πc r.val * (if M[r.val]? = some i then 1 else 0))
        = (lam * πc r.val * ((1 - q i) * d i)) * (if M[r.val]? = some i then 1 else 0) :=
      fun i => by ring
    rw [sum_congr rfl (fun i _ => e i),
      sum_weight_getElem? M (fun i => lam * πc r.val * ((1 - q i) * d i)), getD_map_mul]
    ring
  rw [sum_congr rfl (fun r _ => hrow r), ← mul_sum, Fin.sum_univ_eq_sum_range G (R + 1)]
  congr 1
  have hsub : range (m + 1) ⊆ range (R + 1) := range_subset_range.mpr (by omega)
  rw [← sum_subset hsub (fun n hn hn' => by
    simp only [mem_range] at hn hn'
    simp only [hG, hπc, if_neg (show ¬ n ≤ m by omega), zero_mul]), sum_range_succ]
  congr 1
  · apply sum_congr rfl; intro n hn
    have := mem_range.mp hn
    simp only [hG, hπc]
    rw [if_pos this.le, if_neg this.ne]
    ring
  · simp only [hG, hπc, if_pos le_rfl, if_true]
    rw [List.getD_eq_default _ _ (by simp [hm])]
    ring

end RFL3Aux



namespace RFL3Aux
open ReliableFacilityLoc.Supermod

theorem Phi_eq_hv {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1)
    (S : Finset (Fin J)) (hS : S.card ≤ R) (L : List (Fin J)) (hLnd : L.Nodup)
    (hLS : L.toFinset = S) (hLsort : L.Pairwise (fun a b => d a ≤ d b)) :
    Phi lam d phi q mu R S = lam * hv d phi q L + ∑ j ∈ S, mu j := by
  apply IsLeast.csInf_eq
  refine ⟨upper lam d phi q mu hq0 hq1 R S hS L hLnd hLS, ?_⟩
  rintro v ⟨Y, P, W, hfe, rfl⟩
  exact lower lam d phi q mu hlam hq0 hq1 R S L hLS hLsort Y P W hfe

end RFL3Aux

open ReliableFacilityLoc.Supermod in
theorem solution {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R)
    (S : Finset (Fin J)) (hS : S.card ≤ R) (L : List (Fin J)) (hLnd : L.Nodup)
    (hLS : L.toFinset = S) (hLsort : L.Pairwise (fun a b => d a ≤ d b)) :
    Phi lam d phi q mu R S =
      lam * ∑ k ∈ Icc 1 (countLE d phi L + 1), Ck d phi q L k + ∑ j ∈ S, mu j := by
  rw [RFL3Aux.Phi_eq_hv lam d phi q mu hlam hq0 hq1 S hS L hLnd hLS hLsort,
    RFL3Aux.sumCk_eq d phi q L hLsort]

