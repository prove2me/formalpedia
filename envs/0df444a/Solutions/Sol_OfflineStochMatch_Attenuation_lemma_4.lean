-- Prove2me | solution 1 for OfflineStochMatch.Attenuation.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:50:16.42767+00:00
-- url     : https://prove2.me/submissions/d1cc5996-ed57-41dd-90fe-78a56820985d

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

open OfflineStochMatch.Attenuation
open Filter Topology

private def cardTrue {m : ℕ} (b : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun i => b i = true)).card

private def tailProb (m : ℕ) (x : Fin m → ℝ) (t : ℕ) : ℝ :=
  ∑ b : Fin m → Bool, coinWeight x b * (if cardTrue b < t then 1 else 0)

private def exactProb (m : ℕ) (x : Fin m → ℝ) (r : ℕ) : ℝ :=
  ∑ b : Fin m → Bool, coinWeight x b * (if cardTrue b = r then 1 else 0)

private def flipBit {m : ℕ} (i : Fin m) : (Fin m → Bool) ≃ (Fin m → Bool) where
  toFun b := Function.update b i (!b i)
  invFun b := Function.update b i (!b i)
  left_inv b := by ext j; by_cases h : j = i <;> simp [h]
  right_inv b := by ext j; by_cases h : j = i <;> simp [h]

@[simp] private lemma flipBit_self {m : ℕ} (b : Fin m → Bool) (i : Fin m) :
    flipBit i b i = !b i := by
  simp [flipBit]

@[simp] private lemma flipBit_of_ne {m : ℕ} (b : Fin m → Bool) {i j : Fin m} (h : j ≠ i) :
    flipBit i b j = b j := by
  simp [flipBit, h]

private lemma cardTrue_update_true {m : ℕ} (b : Fin m → Bool) (i : Fin m) (hb : b i = false) :
    cardTrue (Function.update b i true) = cardTrue b + 1 := by
  unfold cardTrue
  have hset : Finset.univ.filter (fun j => Function.update b i true j = true) =
      insert i (Finset.univ.filter (fun j => b j = true)) := by
    ext j
    by_cases hj : j = i <;> simp [hj, hb]
  have hmem : i ∉ Finset.univ.filter (fun j => b j = true) := by simp [hb]
  rw [hset, Finset.card_insert_of_notMem hmem]

private lemma cardTrue_flipBit_of_false {m : ℕ} (b : Fin m → Bool) (i : Fin m) (hb : b i = false) :
    cardTrue (flipBit i b) = cardTrue b + 1 := by
  change cardTrue (Function.update b i (!b i)) = cardTrue b + 1
  rw [hb]
  exact cardTrue_update_true b i hb

private lemma coinWeight_eq_mul_erase {m : ℕ} (x : Fin m → ℝ) (b : Fin m → Bool) (i : Fin m) :
    coinWeight x b = bern (x i) (b i) * ∏ j ∈ Finset.univ.erase i, bern (x j) (b j) := by
  unfold coinWeight
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]

private lemma coinWeight_nonneg {m : ℕ} {x : Fin m → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (b : Fin m → Bool) :
    0 ≤ coinWeight x b := by
  unfold coinWeight
  refine Finset.prod_nonneg fun i _ => ?_
  have hxi := hx i
  cases b i <;> simp [bern] <;> linarith

private lemma exactProb_nonneg {m : ℕ} {x : Fin m → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (r : ℕ) :
    0 ≤ exactProb m x r := by
  unfold exactProb
  refine Finset.sum_nonneg fun b _ => ?_
  have hw := coinWeight_nonneg hx b
  split_ifs <;> linarith

private lemma coinWeight_update_linear {m : ℕ} (x : Fin m → ℝ) (b : Fin m → Bool)
    (i : Fin m) (u : ℝ) :
    coinWeight (Function.update x i u) b =
      (1 - u) * coinWeight (Function.update x i 0) b +
        u * coinWeight (Function.update x i 1) b := by
  rw [coinWeight_eq_mul_erase (Function.update x i u) b i,
      coinWeight_eq_mul_erase (Function.update x i 0) b i,
      coinWeight_eq_mul_erase (Function.update x i 1) b i]
  have hprod : ∀ v : ℝ,
      ∏ j ∈ Finset.univ.erase i, bern (Function.update x i v j) (b j) =
        ∏ j ∈ Finset.univ.erase i, bern (x j) (b j) := by
    intro v
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hprod u, hprod 0, hprod 1]
  simp only [Function.update_self]
  cases b i <;> simp [bern]

private lemma tailProb_update_linear {m : ℕ} (x : Fin m → ℝ) (i : Fin m) (u : ℝ) (t : ℕ) :
    tailProb m (Function.update x i u) t =
      (1 - u) * tailProb m (Function.update x i 0) t +
        u * tailProb m (Function.update x i 1) t := by
  unfold tailProb
  simp only [coinWeight_update_linear x _ i u, add_mul, mul_assoc, Finset.sum_add_distrib,
    ← Finset.mul_sum]

private lemma tailProb_update_one {m : ℕ} (x : Fin m → ℝ) (i : Fin m) (r : ℕ) :
    tailProb m (Function.update x i 1) (r + 1) = tailProb m (Function.update x i 0) r := by
  unfold tailProb
  rw [← (flipBit i).sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coinWeight_eq_mul_erase (Function.update x i 1) (flipBit i b) i,
      coinWeight_eq_mul_erase (Function.update x i 0) b i]
  have hprod : ∏ j ∈ Finset.univ.erase i,
        bern (Function.update x i 1 j) (flipBit i b j) =
      ∏ j ∈ Finset.univ.erase i, bern (Function.update x i 0 j) (b j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne := Finset.ne_of_mem_erase hj
    simp [hne]
  rw [hprod]
  simp only [Function.update_self, flipBit_self]
  by_cases hbi : b i = false
  · rw [cardTrue_flipBit_of_false b i hbi]
    simp [hbi, bern]
  · have hbi' : b i = true := Bool.eq_true_of_not_eq_false hbi
    simp [hbi', bern]

private lemma exactProb_update_one {m : ℕ} (x : Fin m → ℝ) (i : Fin m) (r : ℕ) :
    exactProb m (Function.update x i 1) (r + 1) = exactProb m (Function.update x i 0) r := by
  unfold exactProb
  rw [← (flipBit i).sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coinWeight_eq_mul_erase (Function.update x i 1) (flipBit i b) i,
      coinWeight_eq_mul_erase (Function.update x i 0) b i]
  have hprod : ∏ j ∈ Finset.univ.erase i,
        bern (Function.update x i 1 j) (flipBit i b j) =
      ∏ j ∈ Finset.univ.erase i, bern (Function.update x i 0 j) (b j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne := Finset.ne_of_mem_erase hj
    simp [hne]
  rw [hprod]
  simp only [Function.update_self, flipBit_self]
  by_cases hbi : b i = false
  · rw [cardTrue_flipBit_of_false b i hbi]
    simp [hbi, bern]
  · have hbi' : b i = true := Bool.eq_true_of_not_eq_false hbi
    simp [hbi', bern]

private lemma tailProb_succ_sub {m : ℕ} (x : Fin m → ℝ) (r : ℕ) :
    tailProb m x (r + 1) - tailProb m x r = exactProb m x r := by
  unfold tailProb exactProb
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_sub]
  congr 1
  split_ifs <;> first | omega | norm_num

private lemma tailProb_two_update_diff {m : ℕ} (x : Fin m → ℝ) {i j : Fin m} (hij : i ≠ j)
    (u1 v1 u2 v2 : ℝ) (hsum : u1 + v1 = u2 + v2) (r : ℕ) :
    let y := Function.update (Function.update x i 0) j 0
    tailProb m (Function.update (Function.update x i u1) j v1) (r + 2) -
      tailProb m (Function.update (Function.update x i u2) j v2) (r + 2) =
      (u1 * v1 - u2 * v2) * (exactProb m y (r + 1) - exactProb m y r) := by
  intro y
  have expand : ∀ u v : ℝ,
      tailProb m (Function.update (Function.update x i u) j v) (r + 2) =
        (1 - u) * (1 - v) * tailProb m y (r + 2) +
        (u * (1 - v) + (1 - u) * v) * tailProb m y (r + 1) +
        u * v * tailProb m y r := by
    intro u v
    rw [tailProb_update_linear _ j v (r + 2)]
    rw [Function.update_comm hij u 0 x, tailProb_update_linear _ i u (r + 2)]
    rw [Function.update_comm hij u 1 x, tailProb_update_linear _ i u (r + 2)]
    have h00 : Function.update (Function.update x j 0) i 0 = y :=
      Function.update_comm hij.symm 0 0 x
    have h10 : tailProb m (Function.update (Function.update x j 0) i 1) (r + 2) =
        tailProb m y (r + 1) := by
      rw [tailProb_update_one _ i (r + 1), h00]
    have h01 : tailProb m (Function.update (Function.update x j 1) i 0) (r + 2) =
        tailProb m y (r + 1) := by
      rw [Function.update_comm hij.symm 1 0 x, tailProb_update_one _ j (r + 1)]
    have h11 : tailProb m (Function.update (Function.update x j 1) i 1) (r + 2) =
        tailProb m y r := by
      rw [tailProb_update_one _ i (r + 1), Function.update_comm hij.symm 1 0 x,
        tailProb_update_one _ j r]
    rw [h00, h10, h01, h11]
    ring
  rw [expand u1 v1, expand u2 v2]
  have he1 : tailProb m y (r + 2) = tailProb m y (r + 1) + exactProb m y (r + 1) := by
    linarith [tailProb_succ_sub y (r + 1)]
  have he0 : tailProb m y (r + 1) = tailProb m y r + exactProb m y r := by
    linarith [tailProb_succ_sub y r]
  have hu1 : u1 = u2 + v2 - v1 := by linarith
  rw [he1, he0, hu1]
  ring

/-! ### Exact probability ratio for `{0, p}` and `{0, p, 1}` vectors -/

private lemma exactProb_le_of_zero_or_p {m : ℕ} (y : Fin m → ℝ) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hy : ∀ l, y l = 0 ∨ y l = p) (r : ℕ)
    (hsum : ∑ l, y l + p ≤ (r : ℝ) + 1) :
    exactProb m y (r + 1) ≤ exactProb m y r := by
  let M : Finset (Fin m) := Finset.univ.filter (fun l => y l = p)
  have hy_not_M : ∀ l, l ∉ M → y l = 0 := by
    intro l hl
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rcases hy l with h0 | hp
    · exact h0
    · exact False.elim (hl hp)
  have hcw_zero_of_not_M : ∀ (b : Fin m → Bool) (l : Fin m),
      l ∉ M → b l = true → coinWeight y b = 0 := by
    intro b l hl hbl
    rw [coinWeight_eq_mul_erase y b l, hy_not_M l hl, hbl]
    simp [bern]
  have hsum_true : ∀ b : Fin m → Bool,
      coinWeight y b * (∑ l ∈ M, if b l = true then (1 : ℝ) else 0) =
        coinWeight y b * (cardTrue b : ℝ) := by
    intro b
    by_cases hcw : coinWeight y b = 0
    · simp [hcw]
    · congr 1
      have hsub : Finset.univ.filter (fun l => b l = true) ⊆ M := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
        by_contra hnotM
        exact hcw (hcw_zero_of_not_M b l hnotM hl)
      have hcard : (M.filter (fun l => b l = true)).card = cardTrue b := by
        unfold cardTrue
        congr 1
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨hsub (by simp [h]), h⟩⟩
      simp [← hcard]
  have hsum_false : ∀ b : Fin m → Bool,
      coinWeight y b * (∑ l ∈ M, if b l = false then (1 : ℝ) else 0) =
        coinWeight y b * ((M.card : ℝ) - (cardTrue b : ℝ)) := by
    intro b
    have h1 := hsum_true b
    have h2 : ∀ l ∈ M, (if b l = false then (1 : ℝ) else 0) +
        (if b l = true then (1 : ℝ) else 0) = 1 := by
      intro l _
      cases b l <;> simp
    have h3 : (∑ l ∈ M, if b l = false then (1 : ℝ) else 0) +
        (∑ l ∈ M, if b l = true then (1 : ℝ) else 0) = (M.card : ℝ) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl h2]
      simp
    have h3' : (∑ l ∈ M, if b l = false then (1 : ℝ) else 0) =
        (M.card : ℝ) - (∑ l ∈ M, if b l = true then (1 : ℝ) else 0) := by
      linarith [h3]
    rw [h3', mul_sub, h1, mul_sub]
  have hflip_l : ∀ l ∈ M,
      (1 - p) * (∑ b : Fin m → Bool, coinWeight y b *
          (if b l = true then 1 else 0) * (if cardTrue b = r + 1 then 1 else 0)) =
      p * (∑ b : Fin m → Bool, coinWeight y b *
          (if b l = false then 1 else 0) * (if cardTrue b = r then 1 else 0)) := by
    intro l hl
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [Finset.mul_sum, Finset.mul_sum, ← (flipBit l).sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [coinWeight_eq_mul_erase y (flipBit l b) l,
        coinWeight_eq_mul_erase y b l, hl]
    have hprod : ∏ j ∈ Finset.univ.erase l, bern (y j) (flipBit l b j) =
        ∏ j ∈ Finset.univ.erase l, bern (y j) (b j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [flipBit_of_ne b (Finset.ne_of_mem_erase hj)]
    rw [hprod]
    simp only [flipBit_self]
    by_cases hbl : b l = false
    · rw [cardTrue_flipBit_of_false b l hbl]
      simp [hbl, bern]
      ring
    · have hbl' : b l = true := Bool.eq_true_of_not_eq_false hbl
      simp [hbl']
  have hLHS : ∑ l ∈ M, (1 - p) * (∑ b : Fin m → Bool, coinWeight y b *
        (if b l = true then 1 else 0) * (if cardTrue b = r + 1 then 1 else 0)) =
      (1 - p) * ((r : ℝ) + 1) * exactProb m y (r + 1) := by
    rw [← Finset.mul_sum, Finset.sum_comm, mul_assoc]
    congr 1
    unfold exactProb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have htr := hsum_true b
    have : ∑ x ∈ M, coinWeight y b * (if b x = true then 1 else 0) *
        (if cardTrue b = r + 1 then 1 else 0) =
      coinWeight y b * (∑ x ∈ M, if b x = true then 1 else 0) *
        (if cardTrue b = r + 1 then 1 else 0) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [this, htr]
    split_ifs with hc
    · rw [hc]; push_cast; ring
    · ring
  have hRHS : ∑ l ∈ M, p * (∑ b : Fin m → Bool, coinWeight y b *
        (if b l = false then 1 else 0) * (if cardTrue b = r then 1 else 0)) =
      p * ((M.card : ℝ) - (r : ℝ)) * exactProb m y r := by
    rw [← Finset.mul_sum, Finset.sum_comm, mul_assoc]
    congr 1
    unfold exactProb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hfl := hsum_false b
    have : ∑ x ∈ M, coinWeight y b * (if b x = false then 1 else 0) *
        (if cardTrue b = r then 1 else 0) =
      coinWeight y b * (∑ x ∈ M, if b x = false then 1 else 0) *
        (if cardTrue b = r then 1 else 0) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [this, hfl]
    split_ifs with hc
    · rw [hc]; ring
    · ring
  have heq : (1 - p) * ((r : ℝ) + 1) * exactProb m y (r + 1) =
      p * ((M.card : ℝ) - (r : ℝ)) * exactProb m y r := by
    rw [← hLHS, ← hRHS]
    exact Finset.sum_congr rfl hflip_l
  have hsum_y : ∑ l, y l = (M.card : ℝ) * p := by
    rw [← Finset.sum_subset (Finset.subset_univ M)]
    · have : ∀ l ∈ M, y l = p := fun l hl => (Finset.mem_filter.mp hl).2
      rw [Finset.sum_congr rfl this]
      simp
    · intro l _ hl
      exact hy_not_M l hl
  have hMp : (M.card : ℝ) * p + p ≤ (r : ℝ) + 1 := by linarith
  have hcoeff : p * ((M.card : ℝ) - (r : ℝ)) ≤ (1 - p) * ((r : ℝ) + 1) := by nlinarith
  have hnonneg : 0 ≤ exactProb m y r := by
    refine exactProb_nonneg (fun l => ?_) r
    rcases hy l with h0 | hp
    · rw [h0]; exact ⟨le_refl 0, zero_le_one⟩
    · rw [hp]; exact ⟨le_of_lt hp0, le_of_lt hp1⟩
  have hpos : 0 < (1 - p) * ((r : ℝ) + 1) := by positivity
  nlinarith

private lemma exactProb_le_of_zero_p_one :
    ∀ (c : ℕ) {m : ℕ} (y : Fin m → ℝ) (p : ℝ),
      0 < p → p < 1 →
      (∀ l, y l = 0 ∨ y l = p ∨ y l = 1) →
      (Finset.univ.filter (fun l => y l = 1)).card = c →
      ∀ (r : ℕ), ∑ l, y l + p ≤ (r : ℝ) + 1 →
      exactProb m y (r + 1) ≤ exactProb m y r
  | 0, m, y, p, hp0, hp1, hy, hcard, r, hsum => by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard
    have hy0p : ∀ l, y l = 0 ∨ y l = p := by
      intro l
      rcases hy l with h0 | hp | h1
      · exact Or.inl h0
      · exact Or.inr hp
      · exact False.elim (hcard (Finset.mem_univ l) h1)
    exact exactProb_le_of_zero_or_p y p hp0 hp1 hy0p r hsum
  | c + 1, m, y, p, hp0, hp1, hy, hcard, r, hsum => by
    have hne : (Finset.univ.filter (fun l => y l = 1)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hne
    have hyi : y i = 1 := (Finset.mem_filter.mp hi).2
    have hy_nonneg : ∀ l, 0 ≤ y l := by
      intro l
      rcases hy l with h0 | hp | h1 <;> linarith
    have hy_ge_one : 1 ≤ ∑ l, y l := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hyi]
      have : 0 ≤ ∑ l ∈ Finset.univ.erase i, y l :=
        Finset.sum_nonneg fun l _ => hy_nonneg l
      linarith
    rcases r with _ | r'
    · push_cast at hsum; linarith
    · let y' := Function.update y i 0
      have hy_eq : Function.update y i 1 = y := by
        ext l; by_cases hl : l = i <;> simp [hl, hyi]
      have he1 : exactProb m y (r' + 2) = exactProb m y' (r' + 1) := by
        rw [← hy_eq, exactProb_update_one y i (r' + 1)]
      have he0 : exactProb m y (r' + 1) = exactProb m y' r' := by
        rw [← hy_eq, exactProb_update_one y i r']
      rw [he1, he0]
      have hy' : ∀ l, y' l = 0 ∨ y' l = p ∨ y' l = 1 := by
        intro l
        by_cases hl : l = i
        · subst hl; simp [y']
        · simp [y', hl, hy l]
      have hfilter : Finset.univ.filter (fun l => y' l = 1) =
          (Finset.univ.filter (fun l => y l = 1)).erase i := by
        ext l
        by_cases hl : l = i <;> simp [y', hl]
      have hcard' : (Finset.univ.filter (fun l => y' l = 1)).card = c := by
        rw [hfilter, Finset.card_erase_of_mem hi, hcard]
        omega
      have hsum_y' : ∑ l, y' l = ∑ l, y l - 1 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        rw [← Finset.add_sum_erase _ y (Finset.mem_univ i)]
        have : ∑ l ∈ Finset.univ.erase i, y' l = ∑ l ∈ Finset.univ.erase i, y l := by
          refine Finset.sum_congr rfl fun l hl => ?_
          simp [y', Finset.ne_of_mem_erase hl]
        rw [this, hyi]
        simp [y']
      have hsum' : ∑ l, y' l + p ≤ (r' : ℝ) + 1 := by
        push_cast at hsum ⊢
        linarith
      exact exactProb_le_of_zero_p_one c y' p hp0 hp1 hy' hcard' r' hsum'

/-! ### Sum and squared-norm helpers for two-coordinate updates -/

private lemma sum_two_update {m : ℕ} (x : Fin m → ℝ) {i j : Fin m} (hij : i ≠ j)
    (u v : ℝ) :
    ∑ l, Function.update (Function.update x i u) j v l =
      ∑ l, x l - x i - x j + u + v := by
  have h1 : ∀ (z : Fin m → ℝ) (a : Fin m) (val : ℝ),
      ∑ l, Function.update z a val l = ∑ l, z l - z a + val := by
    intro z a val
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    rw [← Finset.add_sum_erase _ z (Finset.mem_univ a)]
    have : ∑ l ∈ Finset.univ.erase a, Function.update z a val l =
        ∑ l ∈ Finset.univ.erase a, z l := by
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rw [this, Function.update_self]
    ring
  rw [h1 _ j v, h1 x i u, Function.update_of_ne hij.symm]
  ring

private lemma sum_sq_two_update {m : ℕ} (x : Fin m → ℝ) {i j : Fin m} (hij : i ≠ j)
    (u v : ℝ) :
    ∑ l, (Function.update (Function.update x i u) j v l) ^ 2 =
      ∑ l, (x l) ^ 2 - (x i) ^ 2 - (x j) ^ 2 + u ^ 2 + v ^ 2 := by
  have h1 : ∀ (z : Fin m → ℝ) (a : Fin m) (val : ℝ),
      ∑ l, (Function.update z a val l) ^ 2 = ∑ l, (z l) ^ 2 - (z a) ^ 2 + val ^ 2 := by
    intro z a val
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    rw [← Finset.add_sum_erase _ (fun l => (z l) ^ 2) (Finset.mem_univ a)]
    have : ∑ l ∈ Finset.univ.erase a, (Function.update z a val l) ^ 2 =
        ∑ l ∈ Finset.univ.erase a, (z l) ^ 2 := by
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rw [this, Function.update_self]
    ring
  rw [h1 _ j v, h1 x i u, Function.update_of_ne hij.symm]
  ring

/-! ### Step 4: Uniform lower bound on the simplex slice -/

private lemma continuous_tailProb (m : ℕ) (t : ℕ) :
    Continuous (fun x : Fin m → ℝ => tailProb m x t) := by
  unfold tailProb coinWeight
  refine continuous_finsetSum _ fun b _ => ?_
  refine Continuous.mul ?_ continuous_const
  refine continuous_finsetProd _ fun i _ => ?_
  have hci : Continuous (fun x : Fin m → ℝ => x i) := continuous_apply i
  cases b i <;> dsimp [bern]
  · exact continuous_const.sub hci
  · exact hci

private lemma tailProb_uniform_le {m : ℕ} (hm : 1 ≤ m) (x : Fin m → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (r : ℕ)
    (hμ : ∑ i, x i < (r : ℝ) + 1) :
    tailProb m (fun _ => (∑ i, x i) / (m : ℝ)) (r + 2) ≤ tailProb m x (r + 2) := by
  let μ := ∑ i, x i
  let S : Set (Fin m → ℝ) := {z | (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i = μ}
  have hxS : x ∈ S := ⟨hx, rfl⟩
  have hS_sub : S ⊆ Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) 1) := by
    intro z hz i _
    exact hz.1 i
  have hS_closed : IsClosed S := by
    have hS_eq : S = (⋂ i : Fin m, {z : Fin m → ℝ | 0 ≤ z i} ∩ {z : Fin m → ℝ | z i ≤ 1}) ∩
        {z : Fin m → ℝ | ∑ i, z i = μ} := by
      ext z; simp [S]
    rw [hS_eq]
    refine IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun i => IsClosed.inter
        (isClosed_le continuous_const (continuous_apply i))
        (isClosed_le (continuous_apply i) continuous_const)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  have hS_compact : IsCompact S :=
    IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc) hS_closed hS_sub
  obtain ⟨z0, hz0S, hz0_min⟩ :=
    hS_compact.exists_isMinOn ⟨x, hxS⟩ (continuous_tailProb m (r + 2)).continuousOn
  let M1 : Set (Fin m → ℝ) := {z | z ∈ S ∧ tailProb m z (r + 2) ≤ tailProb m z0 (r + 2)}
  have hz0M1 : z0 ∈ M1 := ⟨hz0S, le_refl _⟩
  have hM1_closed : IsClosed M1 :=
    hS_closed.inter (isClosed_le (continuous_tailProb m (r + 2)) continuous_const)
  have hM1_compact : IsCompact M1 :=
    IsCompact.of_isClosed_subset hS_compact hM1_closed (fun z hz => hz.1)
  have hQ_cont : Continuous (fun z : Fin m → ℝ => ∑ i : Fin m, (z i) ^ 2) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2
  obtain ⟨xStar, hxStarM1, hxStar_minQ⟩ :=
    hM1_compact.exists_isMinOn ⟨z0, hz0M1⟩ hQ_cont.continuousOn
  have hxStarS : xStar ∈ S := hxStarM1.1
  have hxStar_le : ∀ z ∈ S, tailProb m xStar (r + 2) ≤ tailProb m z (r + 2) :=
    fun z hz => le_trans hxStarM1.2 (hz0_min hz)
  have havg_contra : ∀ (i j : Fin m), xStar i < xStar j →
      exactProb m (Function.update (Function.update xStar i 0) j 0) (r + 1) ≤
        exactProb m (Function.update (Function.update xStar i 0) j 0) r → False := by
    intro i j hij_lt hD
    have hij : i ≠ j := fun heq => by subst heq; linarith
    let a := (xStar i + xStar j) / 2
    let z' := Function.update (Function.update xStar i a) j a
    have hz'S : z' ∈ S := by
      have hxi := hxStarS.1 i
      have hxj := hxStarS.1 j
      refine ⟨?_, ?_⟩
      · intro l
        by_cases hlj : l = j
        · rw [hlj]; simp [z', a]
          constructor <;> linarith
        · by_cases hli : l = i
          · rw [hli]; simp [z', hij, a]
            constructor <;> linarith
          · simp [z', hlj, hli, hxStarS.1 l]
      · rw [sum_two_update xStar hij a a, hxStarS.2]
        dsimp [a]; ring
    have hdiff := tailProb_two_update_diff xStar hij a a (xStar i) (xStar j) (by dsimp [a]; ring) r
    have hprod_gt : xStar i * xStar j < a * a := by
      dsimp [a]
      have : 0 < (xStar j - xStar i) ^ 2 := sq_pos_of_pos (by linarith)
      nlinarith
    have htail_le : tailProb m z' (r + 2) ≤ tailProb m xStar (r + 2) := by
      have : z' = Function.update (Function.update xStar i a) j a := rfl
      have hupd_self : Function.update (Function.update xStar i (xStar i)) j (xStar j) = xStar := by
        simp
      rw [hupd_self] at hdiff
      nlinarith
    have hz'M1 : z' ∈ M1 := ⟨hz'S, le_trans htail_le hxStarM1.2⟩
    have hQ_le : ∑ l, (xStar l) ^ 2 ≤ ∑ l, (z' l) ^ 2 := hxStar_minQ hz'M1
    have hQ_diff := sum_sq_two_update xStar hij a a
    have hsq_lt : a ^ 2 + a ^ 2 < (xStar i) ^ 2 + (xStar j) ^ 2 := by
      dsimp [a]
      have : 0 < (xStar j - xStar i) ^ 2 := sq_pos_of_pos (by linarith)
      nlinarith
    linarith
  have hno_two_interior : ∀ (i j : Fin m),
      0 < xStar i → xStar i < xStar j → xStar j < 1 → False := by
    intro i j hxi0 hij_lt hxj1
    have hij : i ≠ j := fun heq => by subst heq; linarith
    let y := Function.update (Function.update xStar i 0) j 0
    by_cases hD : exactProb m y (r + 1) ≤ exactProb m y r
    · exact havg_contra i j hij_lt hD
    · have hD' : exactProb m y r < exactProb m y (r + 1) := not_le.mp hD
      let ε := min (xStar i) (1 - xStar j)
      have hε_pos : 0 < ε := lt_min hxi0 (by linarith)
      have hε_le_i : ε ≤ xStar i := min_le_left _ _
      have hε_le_j : ε ≤ 1 - xStar j := min_le_right _ _
      let u1 := xStar i - ε
      let v1 := xStar j + ε
      let z' := Function.update (Function.update xStar i u1) j v1
      have hz'S : z' ∈ S := by
        have hxi := hxStarS.1 i
        have hxj := hxStarS.1 j
        refine ⟨?_, ?_⟩
        · intro l
          by_cases hlj : l = j
          · rw [hlj]; simp [z', v1]
            constructor <;> linarith
          · by_cases hli : l = i
            · rw [hli]; simp [z', hij, u1]
              constructor <;> linarith
            · simp [z', hlj, hli, hxStarS.1 l]
        · rw [sum_two_update xStar hij u1 v1, hxStarS.2]
          dsimp [u1, v1]; ring
      have hdiff := tailProb_two_update_diff xStar hij u1 v1 (xStar i) (xStar j)
        (by dsimp [u1, v1]; ring) r
      have hupd_self : Function.update (Function.update xStar i (xStar i)) j (xStar j) = xStar := by
        simp
      rw [hupd_self] at hdiff
      have hprod_lt : u1 * v1 < xStar i * xStar j := by
        dsimp [u1, v1]
        nlinarith
      have htail_lt : tailProb m z' (r + 2) < tailProb m xStar (r + 2) := by
        nlinarith
      have hge := hxStar_le z' hz'S
      linarith
  have hxStar_const : ∀ i j : Fin m, xStar i = xStar j := by
    intro i j
    by_contra hne
    wlog hij_lt : xStar i < xStar j generalizing i j
    · exact this j i (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hij_lt) (Ne.symm hne))
    have hij : i ≠ j := fun heq => by subst heq; linarith
    let y := Function.update (Function.update xStar i 0) j 0
    by_cases hex_int : ∃ l0 : Fin m, 0 < xStar l0 ∧ xStar l0 < 1
    · obtain ⟨l0, hl0_pos, hl0_lt1⟩ := hex_int
      let p := xStar l0
      have hxStar_0p1 : ∀ l : Fin m, xStar l = 0 ∨ xStar l = p ∨ xStar l = 1 := by
        intro l
        have hxl := hxStarS.1 l
        rcases eq_or_lt_of_le hxl.1 with h0 | hpos
        · exact Or.inl h0.symm
        · rcases eq_or_lt_of_le hxl.2 with h1 | hlt1
          · exact Or.inr (Or.inr h1)
          · refine Or.inr (Or.inl ?_)
            by_contra hnep
            rcases lt_or_gt_of_ne hnep with hlt | hgt
            · exact hno_two_interior l l0 hpos hlt hl0_lt1
            · exact hno_two_interior l0 l hl0_pos hgt hlt1
      have hy_0p1 : ∀ l : Fin m, y l = 0 ∨ y l = p ∨ y l = 1 := by
        intro l
        by_cases hlj : l = j
        · subst hlj; simp [y]
        · by_cases hli : l = i
          · subst hli; simp [y, hlj]
          · simp [y, hlj, hli, hxStar_0p1 l]
      have hxj_ge_p : p ≤ xStar j := by
        have hxi_nonneg := (hxStarS.1 i).1
        rcases hxStar_0p1 j with hj0 | hjp | hj1
        · linarith
        · linarith
        · linarith
      have hsum_y : ∑ l, y l = μ - xStar i - xStar j := by
        rw [sum_two_update xStar hij 0 0, hxStarS.2]; ring
      have hsum_yp : ∑ l, y l + p ≤ (r : ℝ) + 1 := by
        have hxi_nonneg := (hxStarS.1 i).1
        linarith
      have hD := exactProb_le_of_zero_p_one
        (Finset.univ.filter (fun l => y l = 1)).card y p hl0_pos hl0_lt1 hy_0p1 rfl r hsum_yp
      exact havg_contra i j hij_lt hD
    · push Not at hex_int
      have hxStar_01 : ∀ l : Fin m, xStar l = 0 ∨ xStar l = 1 := by
        intro l
        have hxl := hxStarS.1 l
        rcases eq_or_lt_of_le hxl.1 with h0 | hpos
        · exact Or.inl h0.symm
        · exact Or.inr (le_antisymm hxl.2 (hex_int l hpos))
      have hxi0 : xStar i = 0 := by
        rcases hxStar_01 i with h0 | h1
        · exact h0
        · have := (hxStarS.1 j).2; linarith
      have hxj1 : xStar j = 1 := by
        rcases hxStar_01 j with h0 | h1
        · linarith
        · exact h1
      have hy_0p1 : ∀ l : Fin m, y l = 0 ∨ y l = (1 / 2 : ℝ) ∨ y l = 1 := by
        intro l
        by_cases hlj : l = j
        · subst hlj; simp [y]
        · by_cases hli : l = i
          · subst hli; simp [y, hlj]
          · simp only [y, Function.update_of_ne hlj, Function.update_of_ne hli]
            rcases hxStar_01 l with h0 | h1
            · exact Or.inl h0
            · exact Or.inr (Or.inr h1)
      have hsum_y : ∑ l, y l = μ - 1 := by
        rw [sum_two_update xStar hij 0 0, hxStarS.2, hxi0, hxj1]; ring
      have hsum_yp : ∑ l, y l + (1 / 2 : ℝ) ≤ (r : ℝ) + 1 := by linarith
      have hD := exactProb_le_of_zero_p_one
        (Finset.univ.filter (fun l => y l = 1)).card y (1 / 2) (by norm_num) (by norm_num)
        hy_0p1 rfl r hsum_yp
      exact havg_contra i j hij_lt hD
  have i0 : Fin m := ⟨0, hm⟩
  have hsum_const : μ = (m : ℝ) * xStar i0 := by
    rw [← hxStarS.2]
    have : ∀ i : Fin m, xStar i = xStar i0 := fun i => hxStar_const i i0
    simp [this]
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hxStar_eq : xStar = (fun _ : Fin m => μ / (m : ℝ)) := by
    ext i
    rw [hxStar_const i i0, hsum_const, mul_div_cancel_left₀ _ hm_ne]
  rw [← hxStar_eq]
  exact hxStar_le x hxS

/-! ### Step 5: Binomial CDF formula via active coordinate subsets -/

private def indVec {m : ℕ} (S : Finset (Fin m)) (p : ℝ) : Fin m → ℝ :=
  fun i => if i ∈ S then p else 0

private lemma tailProb_zero_vec (m : ℕ) (t : ℕ) :
    tailProb m (fun _ => 0) t = if 0 < t then 1 else 0 := by
  unfold tailProb
  have hsum : ∑ b : Fin m → Bool, coinWeight (fun _ : Fin m => 0) b * (if cardTrue b < t then 1 else 0) =
      coinWeight (fun _ : Fin m => 0) (fun _ : Fin m => false) *
        (if cardTrue (fun _ : Fin m => false) < t then 1 else 0) := by
    refine Finset.sum_eq_single (fun _ => false) ?_ ?_
    · intro b _ hb
      have hex : ∃ i : Fin m, b i = true := by
        by_contra hno
        push Not at hno
        apply hb
        ext i
        simpa using hno i
      obtain ⟨i, hi⟩ := hex
      rw [coinWeight_eq_mul_erase (fun _ => 0) b i, hi]
      simp [bern]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  rw [hsum]
  have hcw : coinWeight (fun _ : Fin m => 0) (fun _ => false) = 1 := by
    unfold coinWeight
    simp [bern]
  have hcard : cardTrue (fun _ : Fin m => false) = 0 := by
    simp [cardTrue]
  rw [hcw, hcard, one_mul]

private lemma tailProb_indVec {m : ℕ} (S : Finset (Fin m)) (p : ℝ) :
    ∀ t : ℕ,
      tailProb m (indVec S p) t =
        ∑ s ∈ Finset.range t, (S.card.choose s : ℝ) * p ^ s * (1 - p) ^ (S.card - s) := by
  induction S using Finset.induction_on with
  | empty =>
    intro t
    have hind : indVec (∅ : Finset (Fin m)) p = (fun _ => 0) := by
      ext i; simp [indVec]
    rw [hind, tailProb_zero_vec, Finset.card_empty]
    rcases t with _ | t
    · simp
    · rw [Finset.sum_range_succ']
      have h0 : ∑ k ∈ Finset.range t,
          ((Nat.choose 0 (k + 1) : ℝ) * p ^ (k + 1) * (1 - p) ^ (0 - (k + 1))) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        simp
      rw [h0]
      simp
  | @insert i S hi ih =>
    intro t
    rcases t with _ | t
    · simp [tailProb]
    · have hupd_p : Function.update (indVec S p) i p = indVec (insert i S) p := by
        ext j; by_cases hj : j = i <;> simp [indVec, hj]
      have hupd_0 : Function.update (indVec S p) i 0 = indVec S p := by
        ext j; by_cases hj : j = i <;> simp [indVec, hj, hi]
      have hrec : tailProb m (indVec (insert i S) p) (t + 1) =
          (1 - p) * tailProb m (indVec S p) (t + 1) + p * tailProb m (indVec S p) t := by
        rw [← hupd_p, tailProb_update_linear _ i p (t + 1),
            tailProb_update_one _ i t, hupd_0]
      rw [hrec, ih (t + 1), ih t, Finset.card_insert_of_notMem hi]
      set c := S.card
      rw [Finset.sum_range_succ' _ t, Finset.sum_range_succ' _ t]
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul, Nat.sub_zero]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      have h0 : (1 - p) * (1 - p) ^ c = (1 - p) ^ (c + 1) := by ring
      have hsum_eq :
          (∑ x ∈ Finset.range t,
            (1 - p) * ((c.choose (x + 1) : ℝ) * p ^ (x + 1) * (1 - p) ^ (c - (x + 1)))) +
          (∑ x ∈ Finset.range t,
            p * ((c.choose x : ℝ) * p ^ x * (1 - p) ^ (c - x))) =
          ∑ k ∈ Finset.range t,
            (((c + 1).choose (k + 1) : ℝ) * p ^ (k + 1) * (1 - p) ^ (c + 1 - (k + 1))) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Nat.choose_succ_succ c s, Nat.cast_add, Nat.succ_sub_succ_eq_sub]
        by_cases hsc : s + 1 ≤ c
        · have hexp : c - s = (c - (s + 1)) + 1 := by omega
          rw [hexp, pow_succ (1 - p), pow_succ p s]
          ring
        · have hchoose0 : c.choose (s + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          rw [hchoose0, Nat.cast_zero, pow_succ p s]
          ring
      linarith

private lemma tailProb_const (m : ℕ) (p : ℝ) (t : ℕ) :
    tailProb m (fun _ => p) t =
      ∑ s ∈ Finset.range t, (m.choose s : ℝ) * p ^ s * (1 - p) ^ (m - s) := by
  have h : (fun _ : Fin m => p) = indVec Finset.univ p := by
    ext i; simp [indVec]
  rw [h, tailProb_indVec, Finset.card_univ, Fintype.card_fin]

/-! ### Step 6: Zero-padding invariance -/

private def padZero {k : ℕ} (q : Fin k → ℝ) (N : ℕ) : Fin N → ℝ :=
  fun i => if h : i.val < k then q ⟨i.val, h⟩ else 0

private def snocBoolEquiv (m : ℕ) : (Bool × (Fin m → Bool)) ≃ (Fin (m + 1) → Bool) where
  toFun p := Fin.snoc p.2 p.1
  invFun b := (b (Fin.last m), fun i => b i.castSucc)
  left_inv p := by
    rcases p with ⟨bl, bf⟩
    ext <;> simp
  right_inv b := by
    ext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

private lemma tailProb_snoc_zero {m : ℕ} (x : Fin m → ℝ) (t : ℕ) :
    tailProb (m + 1) (Fin.snoc x 0) t = tailProb m x t := by
  unfold tailProb
  rw [← (snocBoolEquiv m).sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have htrue : ∑ b : Fin m → Bool,
      coinWeight (Fin.snoc x 0) (snocBoolEquiv m (true, b)) *
      (if cardTrue (snocBoolEquiv m (true, b)) < t then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [coinWeight_eq_mul_erase (Fin.snoc x 0) (snocBoolEquiv m (true, b)) (Fin.last m)]
    simp [snocBoolEquiv, bern]
  rw [htrue, zero_add]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hcw : coinWeight (Fin.snoc x 0) (snocBoolEquiv m (false, b)) = coinWeight x b := by
    unfold coinWeight
    rw [Fin.prod_univ_castSucc]
    simp [snocBoolEquiv, bern]
  have hcard : cardTrue (snocBoolEquiv m (false, b)) = cardTrue b := by
    unfold cardTrue
    have hmap : Finset.univ.filter (fun i : Fin (m + 1) => snocBoolEquiv m (false, b) i = true) =
        (Finset.univ.filter (fun i : Fin m => b i = true)).map Fin.castSuccEmb := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Fin.castSuccEmb_apply]
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [snocBoolEquiv]
    rw [hmap, Finset.card_map]
  rw [hcw, hcard]

private lemma tailProb_padZero {k : ℕ} (q : Fin k → ℝ) (t : ℕ) :
    ∀ d : ℕ, tailProb (k + d) (padZero q (k + d)) t = tailProb k q t
  | 0 => by
    change tailProb k (padZero q k) t = tailProb k q t
    have heq : padZero q k = q := by
      ext i; simp [padZero]
    rw [heq]
  | d + 1 => by
    change tailProb ((k + d) + 1) (padZero q ((k + d) + 1)) t = tailProb k q t
    have hsnoc : padZero q ((k + d) + 1) = Fin.snoc (padZero q (k + d)) 0 := by
      ext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [padZero]
    rw [hsnoc, tailProb_snoc_zero, tailProb_padZero q t d]

private lemma sum_padZero {k : ℕ} (q : Fin k → ℝ) :
    ∀ d : ℕ, ∑ i : Fin (k + d), padZero q (k + d) i = ∑ i : Fin k, q i
  | 0 => by
    change ∑ i : Fin k, padZero q k i = ∑ i : Fin k, q i
    have heq : padZero q k = q := by
      ext i; simp [padZero]
    rw [heq]
  | d + 1 => by
    change ∑ i : Fin ((k + d) + 1), padZero q ((k + d) + 1) i = ∑ i : Fin k, q i
    have hsnoc : padZero q ((k + d) + 1) = Fin.snoc (padZero q (k + d)) 0 := by
      ext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [padZero]
    rw [hsnoc, Fin.sum_univ_castSucc]
    simp [sum_padZero q d]

private lemma padZero_bounds {k : ℕ} {q : Fin k → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (N : ℕ) (i : Fin N) :
    0 ≤ padZero q N i ∧ padZero q N i ≤ 1 := by
  unfold padZero
  split_ifs with h
  · exact hq ⟨i.val, h⟩
  · exact ⟨le_refl 0, zero_le_one⟩

/-! ### Step 7: Limit as `N → ∞` of Binomial probabilities to Poisson probabilities -/

private lemma tendsto_choose_mul_div_pow (μ : ℝ) :
    ∀ s : ℕ,
      Tendsto (fun N : ℕ => (N.choose s : ℝ) * (μ / (N : ℝ)) ^ s)
        atTop (𝓝 (μ ^ s / (s.factorial : ℝ)))
  | 0 => by
    simp
  | s + 1 => by
    have hrec : ∀ᶠ N : ℕ in atTop,
        (N.choose (s + 1) : ℝ) * (μ / (N : ℝ)) ^ (s + 1) =
          ((N.choose s : ℝ) * (μ / (N : ℝ)) ^ s) *
            ((μ / ((s : ℝ) + 1)) * (1 - (s : ℝ) / (N : ℝ))) := by
      filter_upwards [eventually_ge_atTop (s + 1)] with N hN
      have hN_pos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hs1_pos : (s : ℝ) + 1 ≠ 0 := by positivity
      have hchoose : (N.choose (s + 1) : ℝ) * ((s : ℝ) + 1) =
          (N.choose s : ℝ) * ((N : ℝ) - (s : ℝ)) := by
        have hnat := Nat.choose_succ_right_eq N s
        have hcast : ((N.choose (s + 1) * (s + 1) : ℕ) : ℝ) =
            ((N.choose s * (N - s) : ℕ) : ℝ) := by rw [hnat]
        have hle : s ≤ N := by omega
        push_cast [Nat.cast_sub hle] at hcast
        exact hcast
      have hchoose_div : (N.choose (s + 1) : ℝ) =
          (N.choose s : ℝ) * ((N : ℝ) - (s : ℝ)) / ((s : ℝ) + 1) := by
        rw [← hchoose, mul_div_cancel_right₀ _ hs1_pos]
      rw [hchoose_div, pow_succ]
      field_simp
    rw [tendsto_congr' hrec]
    have h1 := tendsto_choose_mul_div_pow μ s
    have h2 : Tendsto (fun N : ℕ => (μ / ((s : ℝ) + 1)) * (1 - (s : ℝ) / (N : ℝ)))
        atTop (𝓝 ((μ / ((s : ℝ) + 1)) * (1 - 0))) := by
      refine tendsto_const_nhds.mul ?_
      refine tendsto_const_nhds.sub ?_
      exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hprod := h1.mul h2
    have heq : (μ ^ s / (s.factorial : ℝ)) * ((μ / ((s : ℝ) + 1)) * (1 - 0)) =
        μ ^ (s + 1) / ((s + 1).factorial : ℝ) := by
      have hsf : (s.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
      have hs1 : (s : ℝ) + 1 ≠ 0 := by positivity
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
      ring
    rwa [heq] at hprod

private lemma tendsto_one_sub_div_pow_sub (μ : ℝ) (s : ℕ) :
    Tendsto (fun N : ℕ => (1 - μ / (N : ℝ)) ^ (N - s))
      atTop (𝓝 (Real.exp (-μ))) := by
  obtain ⟨M, hM⟩ := exists_nat_gt |μ|
  have hev : ∀ᶠ N : ℕ in atTop,
      (1 - μ / (N : ℝ)) ^ (N - s) =
        (1 + -μ / (N : ℝ)) ^ N / (1 - μ / (N : ℝ)) ^ s := by
    filter_upwards [eventually_ge_atTop (max s (M + 1))] with N hN
    have hs : s ≤ N := le_trans (le_max_left _ _) hN
    have hM1 : M + 1 ≤ N := le_trans (le_max_right _ _) hN
    have hN_gt : |μ| < (N : ℝ) := lt_of_lt_of_le hM (by exact_mod_cast le_trans (Nat.le_succ M) hM1)
    have hμ_lt : μ < (N : ℝ) := lt_of_le_of_lt (le_abs_self μ) hN_gt
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    have hbase_ne : 1 - μ / (N : ℝ) ≠ 0 := by
      intro h0
      have hdiv : μ / (N : ℝ) = 1 := by linarith
      have hμN : μ = 1 * (N : ℝ) := (div_eq_iff hN_pos.ne').mp hdiv
      linarith
    have h1 : 1 + -μ / (N : ℝ) = 1 - μ / (N : ℝ) := by ring
    rw [h1, pow_sub₀ _ hbase_ne hs, ← div_eq_mul_inv]
  rw [tendsto_congr' hev]
  have hnum : Tendsto (fun N : ℕ => (1 + -μ / (N : ℝ)) ^ N) atTop (𝓝 (Real.exp (-μ))) :=
    Real.tendsto_one_add_div_pow_exp (-μ)
  have hden : Tendsto (fun N : ℕ => (1 - μ / (N : ℝ)) ^ s) atTop (𝓝 ((1 - 0) ^ s)) := by
    refine Tendsto.pow ?_ s
    exact tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  have hden1 : ((1 : ℝ) - 0) ^ s = 1 := by ring
  rw [hden1] at hden
  have hdiv : Tendsto (fun N : ℕ => (1 + -μ / (N : ℝ)) ^ N / (1 - μ / (N : ℝ)) ^ s)
      atTop (𝓝 (Real.exp (-μ) / 1)) :=
    Filter.Tendsto.div hnum hden one_ne_zero
  rwa [div_one] at hdiv

private lemma tendsto_binom_cdf_poisson (μ : ℝ) (t : ℕ) :
    Tendsto (fun N : ℕ =>
        ∑ s ∈ Finset.range t, (N.choose s : ℝ) * (μ / (N : ℝ)) ^ s * (1 - μ / (N : ℝ)) ^ (N - s))
      atTop
      (𝓝 (∑ s ∈ Finset.range t, Real.exp (-μ) * μ ^ s / (s.factorial : ℝ))) := by
  refine tendsto_finsetSum _ fun s _ => ?_
  have h := (tendsto_choose_mul_div_pow μ s).mul (tendsto_one_sub_div_pow_sub μ s)
  have heq : (μ ^ s / (s.factorial : ℝ)) * Real.exp (-μ) =
      Real.exp (-μ) * μ ^ s / (s.factorial : ℝ) := by ring
  rwa [heq] at h

theorem solution (t k : ℕ) (q : Fin k → ℝ) (ht : 1 ≤ t) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hμ : ∑ i, q i < (t : ℝ) - 1) :
    ∑ i ∈ Finset.range t, Real.exp (-(∑ j, q j)) * (∑ j, q j) ^ i / (i.factorial : ℝ)
      ≤ ∑ b : Fin k → Bool,
          coinWeight q b * (if (Finset.univ.filter (fun i => b i = true)).card < t then 1 else 0) := by
  let μ := ∑ j, q j
  have hμ_nonneg : 0 ≤ μ := Finset.sum_nonneg fun i _ => (hq i).1
  rcases t with _ | r
  · omega
  · rcases r with _ | r
    · push_cast at hμ; linarith
    · change ∑ i ∈ Finset.range (r + 2), Real.exp (-μ) * μ ^ i / (i.factorial : ℝ) ≤
        tailProb k q (r + 2)
      have hμ_r : μ < (r : ℝ) + 1 := by
        push_cast at hμ ⊢
        linarith
      have hev_le : ∀ᶠ N : ℕ in atTop,
          (∑ s ∈ Finset.range (r + 2),
            (N.choose s : ℝ) * (μ / (N : ℝ)) ^ s * (1 - μ / (N : ℝ)) ^ (N - s)) ≤
          tailProb k q (r + 2) := by
        filter_upwards [eventually_ge_atTop (k + 1)] with N hN
        have hN1 : 1 ≤ N := by omega
        let d := N - k
        have hkd : k + d = N := by omega
        have hμ_pad : μ = ∑ i : Fin (k + d), padZero q (k + d) i := (sum_padZero q d).symm
        rw [← tailProb_const N (μ / (N : ℝ)) (r + 2), ← hkd]
        rw [← tailProb_padZero q (r + 2) d, hμ_pad]
        exact tailProb_uniform_le (by omega) (padZero q (k + d))
          (padZero_bounds hq (k + d)) r (by rw [← hμ_pad]; exact hμ_r)
      exact le_of_tendsto (tendsto_binom_cdf_poisson μ (r + 2)) hev_le
