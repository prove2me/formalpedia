-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P37.ghzMeasurements
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:40:02.089877+00:00
-- url     : https://prove2.me/submissions/369f1bb9-64ba-4f92-ac5a-96f85da09d04

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37
noncomputable section
open QAlgorithms.Papers.Independent.Renew46.P37
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Claimed50.P33 (InformationKind singleParties allParties)

theorem X7G5_shannon_const {Y : Type} [Fintype Y] (q : Y → ℝ) (c k : ℝ)
    (hc : Real.logb 2 c = -k) (h : ∀ y, q y = 0 ∨ q y = c) (hs : ∑ y, q y = 1) :
    shannon q = k := by
  unfold shannon
  have : ∀ y, q y * Real.logb 2 (q y) = q y * (-k) := by
    intro y; rcases h y with h1 | h1 <;> rw [h1]; simp; rw [hc]
  simp only [this, ← Finset.sum_mul, hs]; ring

theorem X7G5_marg_sum {n : ℕ} (p : CData n) (s : Finset (Fin n)) :
    ∑ a, lawMarginal p s a = ∑ x, p.prob x := by
  unfold lawMarginal
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : ∀ a : (i : {i : Fin n // i ∈ s}) → Fin (p.dims i.val),
      (∀ i : {i : Fin n // i ∈ s}, x i.val = a i) ↔ (fun i : {i : Fin n // i ∈ s} => x i.val) = a := fun a => by
    constructor
    · intro h; funext i; exact h i
    · rintro rfl i; rfl
  simp only [this]
  rw [Finset.sum_ite_eq]; simp

theorem X7G5_cH_val {n : ℕ} (p : CData n) (hp : IsLaw p.prob) (s : Finset (Fin n)) (c k : ℝ)
    (hc : Real.logb 2 c = -k) (h : ∀ a, lawMarginal p s a = 0 ∨ lawMarginal p s a = c) :
    cH p s = k :=
  X7G5_shannon_const _ c k hc h (by rw [X7G5_marg_sum, hp.2])

theorem X7G5_marg {n : ℕ} (p : CData n) (c0 : ℝ) (Q : ClassicalBasis p.dims → Prop)
    [DecidablePred Q] (hp : ∀ x, p.prob x = if Q x then c0 else 0) (s : Finset (Fin n))
    (a : (i : {i : Fin n // i ∈ s}) → Fin (p.dims i.val)) :
    lawMarginal p s a = c0 * (Finset.univ.filter (fun x : ClassicalBasis p.dims =>
      (∀ i : {i : Fin n // i ∈ s}, x i.val = a i) ∧ Q x)).card := by
  unfold lawMarginal
  simp only [hp]
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h1 : ∀ i : {i : Fin n // i ∈ s}, x i.val = a i <;> by_cases h2 : Q x <;> simp [h1, h2]

theorem X7G5_cH_empty {n : ℕ} (p : CData n) (hp : IsValidClassicalData p) :
    cH p ∅ = 0 := by
  have := X7G5_cH_val p hp.2 ∅ 1 0 (by simp) (fun a => Or.inr (by
    unfold lawMarginal
    rw [← hp.2.2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [if_pos]
    intro i; exact absurd i.2 (Finset.notMem_empty _)))
  exact this

theorem X7G5_dual {n : ℕ} (p : CData n) :
    cValue .dual p = (∑ i, cH p (Finset.univ.erase i)) - (n - 1 : ℕ) * cH p Finset.univ := by
  have hs : QAlgorithms.Papers.Independent.Claimed50.P33.singleParties n =
      fun i => ({i} : Finset (Fin n)) := rfl
  simp only [cValue, cInfo, QAlgorithms.Papers.Independent.Claimed50.P33.allParties, hs,
    Finset.biUnion_singleton_eq_self]

theorem X7G5_total {n : ℕ} (p : CData n) :
    cValue .total p = (∑ i, cH p {i}) - cH p Finset.univ := by
  have hs : QAlgorithms.Papers.Independent.Claimed50.P33.singleParties n =
      fun i => ({i} : Finset (Fin n)) := rfl
  simp only [cValue, cInfo, QAlgorithms.Papers.Independent.Claimed50.P33.allParties, hs,
    Finset.biUnion_singleton_eq_self]


theorem X7G5_sum {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .dual p + cValue .total p =
      ∑ i, lawCMI p {i} (Finset.univ.erase i) ∅ := by
  rw [X7G5_dual, X7G5_total]
  have hu : ∀ i : Fin n, {i} ∪ Finset.univ.erase i ∪ ∅ = Finset.univ := by
    intro i; ext j; by_cases h : j = i <;> simp [h]
  simp only [lawCMI, hu, Finset.union_empty, X7G5_cH_empty p hp, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [this]; ring

def X7G5_G {n : ℕ} (p : CData n) (k : ℕ) : ℝ := cH p (Finset.univ.filter fun j : Fin n => j.val < k)

theorem X7G5_tele {m : ℕ} (p : CData (m+1)) (hp : IsValidClassicalData p) :
    ∑ i : Fin m, (X7G5_G p (i.val + 1) - X7G5_G p i.val) =
      cH p (Finset.univ.erase (Fin.last m)) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => X7G5_G p (k + 1) - X7G5_G p k) m,
    Finset.sum_range_sub]
  have h0 : X7G5_G p 0 = 0 := by
    unfold X7G5_G; simpa using X7G5_cH_empty p hp
  rw [h0, sub_zero]; unfold X7G5_G; congr 1; ext j
  simp [Fin.ext_iff, Fin.lt_def] <;> omega

theorem X7G5_S3 {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .dual p = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n),
      lawCMI p {i} (later i) (earlier i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [X7G5_dual, Finset.sum_filter, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, lt_self_iff_false, if_false, add_zero]
  have hc : ∀ i : Fin m, (i.val + 1 < m + 1) = True := fun i => by simp [i.isLt]
  simp only [hc, if_true]
  have e1 : ∀ i : Fin m, {i.castSucc} ∪ earlier i.castSucc =
      Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1 := by
    intro i; ext j; simp [earlier, Fin.ext_iff] <;> omega
  have e2 : ∀ i : Fin m, later i.castSucc ∪ earlier i.castSucc = Finset.univ.erase i.castSucc := by
    intro i; ext j; simp [earlier, later, Fin.ext_iff] <;> omega
  have e3 : ∀ i : Fin m, {i.castSucc} ∪ later i.castSucc ∪ earlier i.castSucc = Finset.univ := by
    intro i; ext j; simp [earlier, later, Fin.ext_iff] <;> omega
  have e4 : ∀ i : Fin m, earlier i.castSucc = Finset.univ.filter fun j : Fin (m+1) => j.val < i.val := by
    intro i; ext j; simp [earlier]
  simp only [lawCMI, e1, e2, e3]
  simp only [e4, Nat.add_sub_cancel]
  have := X7G5_tele p hp
  simp only [X7G5_G] at this
  have h2 : ∑ i : Fin m, (cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1) +
      cH p (Finset.univ.erase i.castSucc) -
      cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val) - cH p Finset.univ) =
      (∑ i : Fin m, (cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1) -
      cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val))) +
      ∑ i : Fin m, cH p (Finset.univ.erase i.castSucc) - m * cH p Finset.univ := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]; ring
  linarith [h2, this]

theorem X7G5_T1 {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .total p = ∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < i.val),
      lawCMI p (earlier i) {i} ∅ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [X7G5_total, Finset.sum_filter,
    Fin.sum_univ_succ (f := fun a => if 0 < a.val then lawCMI p (earlier a) {a} ∅ else 0),
    Fin.sum_univ_succ (f := fun i => cH p {i})]
  simp only [Fin.val_zero, lt_self_iff_false, if_false, zero_add, Fin.val_succ,
    Nat.succ_pos, if_true, lawCMI, Finset.union_empty, X7G5_cH_empty p hp, sub_zero]
  have e1 : ∀ i : Fin m, earlier i.succ = Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1 := by
    intro i; ext j; simp [earlier]
  have e2 : ∀ i : Fin m, earlier i.succ ∪ {i.succ} =
      Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1 + 1 := by
    intro i; ext j; simp [earlier, Fin.ext_iff] <;> omega
  simp only [e2]
  simp only [e1]
  have := Finset.sum_range_sub (fun k => - X7G5_G p (k + 1)) m
  rw [← Fin.sum_univ_eq_sum_range (fun k => - X7G5_G p (k + 1 + 1) - - X7G5_G p (k + 1)) m] at this
  simp only [X7G5_G] at this
  have h0 : cH p {0} = cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < 0 + 1) := by
    congr 1; ext j
    simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff,
      Fin.val_zero]
    omega
  have hm : cH p Finset.univ = cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < m + 1) := by
    congr 1; ext j
    simp only [Finset.mem_univ, Finset.mem_filter, true_and, true_iff]
    exact j.isLt
  have h3 : ∑ i : Fin m, (cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1) +
      cH p {i.succ} - cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1 + 1)) =
      ∑ i : Fin m, cH p {i.succ} + ∑ i : Fin m,
      (-cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1 + 1) -
        -cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1)) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => by ring
  linarith [h3, this, h0, hm]

theorem X7G5_T2 {n : ℕ} (hn : 3 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .total p = cInfo .total p (firstParties n) +
      lawCMI p (Finset.univ.filter fun i => i.val + 1 = n)
        (Finset.univ.filter fun i => i.val + 1 < n) ∅ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hL : (Finset.univ.filter fun i : Fin (m+1) => i.val + 1 = m + 1) = {Fin.last m} := by
    ext j; simp [Fin.ext_iff]
  have hR : (Finset.univ.filter fun i : Fin (m+1) => i.val + 1 < m + 1) =
      Finset.univ.erase (Fin.last m) := by
    ext j; simp [Fin.ext_iff] <;> omega
  have hLR : ({Fin.last m} ∪ Finset.univ.erase (Fin.last m) ∪ ∅ : Finset (Fin (m+1))) = Finset.univ := by
    ext j; by_cases h : j = Fin.last m <;> simp [h]
  have hA : allParties (firstParties (m+1)) = Finset.univ.erase (Fin.last m) := by
    ext j
    simp only [allParties, firstParties, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, Finset.mem_erase, ne_eq, and_true, Fin.ext_iff, Fin.val_last]
    constructor
    · rintro ⟨a, ha⟩; have := a.isLt; omega
    · intro h; exact ⟨⟨j.val, by omega⟩, rfl⟩
  have hsum : ∑ i : Fin (m + 1 - 1), cH p (firstParties (m+1) i) = ∑ i : Fin m, cH p {i.castSucc} := by
    refine Fintype.sum_equiv (finCongr (by omega)) _ _ fun i => ?_
    congr 1; ext j; simp [firstParties, Fin.ext_iff]
  simp only [cInfo, lawCMI, hL, hR, hLR, hA, hsum, Finset.union_empty, X7G5_cH_empty p hp]
  rw [X7G5_total, Fin.sum_univ_castSucc]; ring

theorem X7G5_S4 {n : ℕ} (hn : 3 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .dual p = cInfo .dual p (mergeLast n) +
      lawCMI p (Finset.univ.filter fun i => i.val + 2 = n)
        (Finset.univ.filter fun i => i.val + 1 = n)
        (Finset.univ.filter fun i => i.val + 2 < n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hL1 : (Finset.univ.filter fun i : Fin (k+3) => i.val + 2 = k + 3) =
      {(Fin.last (k+1)).castSucc} := by ext j; simp [Fin.ext_iff] <;> omega
  have hL2 : (Finset.univ.filter fun i : Fin (k+3) => i.val + 1 = k + 3) = {Fin.last (k+2)} := by
    ext j; simp [Fin.ext_iff] <;> omega
  have hE1 : ({(Fin.last (k+1)).castSucc} ∪ (Finset.univ.filter fun i : Fin (k+3) => i.val + 2 < k + 3)
      : Finset (Fin (k+3))) = Finset.univ.erase (Fin.last (k+2)) := by
    ext j; simp [Fin.ext_iff] <;> omega
  have hE2 : ({Fin.last (k+2)} ∪ (Finset.univ.filter fun i : Fin (k+3) => i.val + 2 < k + 3)
      : Finset (Fin (k+3))) = Finset.univ.erase (Fin.last (k+1)).castSucc := by
    ext j; simp [Fin.ext_iff] <;> omega
  have hE3 : ({(Fin.last (k+1)).castSucc} ∪ {Fin.last (k+2)} ∪
      (Finset.univ.filter fun i : Fin (k+3) => i.val + 2 < k + 3) : Finset (Fin (k+3))) =
      Finset.univ := by
    ext j; simp [Fin.ext_iff] <;> omega
  have hA : allParties (mergeLast (k+3)) = Finset.univ := by
    ext j
    simp only [allParties, mergeLast, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, iff_true]
    refine ⟨⟨min j.val (k+1), by omega⟩, ?_⟩
    split_ifs with h <;> simp at h ⊢ <;> omega
  have hG : ∀ i : Fin (k+3-1), (Finset.univ.erase i).biUnion (mergeLast (k+3)) =
      if i.val = k + 1 then Finset.univ.filter (fun j : Fin (k+3) => j.val + 2 < k + 3)
      else Finset.univ.filter (fun j : Fin (k+3) => j.val ≠ i.val) := by
    intro i
    have hi := i.isLt
    split_ifs with h
    · ext j
      simp only [mergeLast, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_filter, true_and, ne_eq]
      have hj0 := j.isLt
      constructor
      · rintro ⟨a, ha, hj⟩
        have := a.isLt
        rw [Fin.ext_iff] at ha
        split_ifs at hj with h' <;> omega
      · intro hj
        refine ⟨⟨j.val, by omega⟩, fun hc => by
          have := congrArg Fin.val hc; rw [Fin.val_mk] at this; omega, ?_⟩
        split_ifs with h' <;> (try simp only [Fin.val_mk] at h' ⊢) <;> omega
    · ext j
      simp only [mergeLast, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_filter, true_and, ne_eq]
      have hj0 := j.isLt
      constructor
      · rintro ⟨a, ha, hj⟩
        have := a.isLt
        rw [Fin.ext_iff] at ha
        split_ifs at hj with h' <;> omega
      · intro hj
        refine ⟨⟨min j.val (k+1), by omega⟩, fun hc => by
          have := congrArg Fin.val hc; rw [Fin.val_mk] at this; omega, ?_⟩
        split_ifs with h' <;> (try simp only [Fin.val_mk] at h' ⊢) <;> omega
  have hsum : ∑ i : Fin (k + 3 - 1), cH p ((Finset.univ.erase i).biUnion (mergeLast (k+3))) =
      (∑ i : Fin (k+1), cH p (Finset.univ.erase i.castSucc.castSucc)) +
      cH p (Finset.univ.filter (fun j : Fin (k+3) => j.val + 2 < k + 3)) := by
    rw [Fintype.sum_equiv (finCongr (by omega : k + 3 - 1 = k + 2)) _
      (fun i : Fin (k+2) => cH p (if i.val = k + 1 then Finset.univ.filter (fun j : Fin (k+3) => j.val + 2 < k + 3)
      else Finset.univ.filter (fun j : Fin (k+3) => j.val ≠ i.val))) (fun i => by rw [hG]; rfl)]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, if_true]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_neg (by have := i.isLt; omega)]
    congr 1; ext j; simp [Fin.ext_iff]
  simp only [cInfo, lawCMI, hL1, hL2, hE1, hE2, hE3, hA, hsum]
  rw [X7G5_dual, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  push_cast
  have h1 : ((k + 3 - 1 - 1 : ℕ) : ℝ) = k + 1 := by
    rw [show k + 3 - 1 - 1 = k + 1 by omega]; push_cast; ring
  have h2 : ((k + 3 - 1 : ℕ) : ℝ) = k + 2 := by
    rw [show k + 3 - 1 = k + 2 by omega]; push_cast; ring
  ring

theorem X7G5_five (p : CData 3) (hp : IsValidClassicalData p) (h0 h1 h2 h01 h02 h12 hU : ℝ)
    (e0 : cH p {0} = h0) (e1 : cH p {1} = h1) (e2 : cH p {2} = h2) (e01 : cH p {0,1} = h01)
    (e02 : cH p {0,2} = h02) (e12 : cH p {1,2} = h12) (eU : cH p Finset.univ = hU) :
    fiveValues p = ![h0 + h12 - hU, h1 + h02 - hU, h2 + h01 - hU, h12 + h02 + h01 - 2*hU,
      h0 + h1 + h2 - hU] := by
  have s1 : ({0} ∪ {1, 2} ∪ ∅ : Finset (Fin 3)) = Finset.univ := by decide
  have s2 : ({1} ∪ {0, 2} ∪ ∅ : Finset (Fin 3)) = Finset.univ := by decide
  have s3 : ({2} ∪ {0, 1} ∪ ∅ : Finset (Fin 3)) = Finset.univ := by decide
  have r0 : (Finset.univ.erase 0 : Finset (Fin 3)) = {1, 2} := by decide
  have r1 : (Finset.univ.erase 1 : Finset (Fin 3)) = {0, 2} := by decide
  have r2 : (Finset.univ.erase 2 : Finset (Fin 3)) = {0, 1} := by decide
  unfold fiveValues lawCMI
  rw [X7G5_dual, X7G5_total, Fin.sum_univ_three, Fin.sum_univ_three, s1, s2, s3, r0, r1, r2]
  simp only [Finset.union_empty, X7G5_cH_empty p hp, e0, e1, e2, e01, e02, e12, eU]
  ext i; fin_cases i <;> simp <;> norm_num <;> ring

theorem X7G5_marg3 (j : Fin 5) (c0 : ℝ) (Q : (Fin 3 → Fin 2) → Prop) [DecidablePred Q]
    (hp : ∀ x : Fin 3 → Fin 2, (exampleLaw j).prob x = if Q x then c0 else 0) (s : Finset (Fin 3))
    (a : (i : {i : Fin 3 // i ∈ s}) → Fin 2) :
    lawMarginal (exampleLaw j) s a = c0 * (Finset.univ.filter (fun x : Fin 3 → Fin 2 =>
      (∀ i : {i : Fin 3 // i ∈ s}, x i.val = a i) ∧ Q x)).card := by
  unfold lawMarginal
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hx := hp x
  by_cases h1 : ∀ i : {i : Fin 3 // i ∈ s}, x i.val = a i
  · by_cases h2 : Q x
    · rw [if_pos h1, hx, if_pos h2, if_pos ⟨h1, h2⟩, Nat.cast_one, mul_one]
    · rw [if_pos h1, hx, if_neg h2, if_neg (fun h => h2 h.2), Nat.cast_zero, mul_zero]
  · rw [if_neg h1, if_neg (fun h => h1 h.1), Nat.cast_zero, mul_zero]

theorem X7G5_val3 (j : Fin 5) (c0 : ℝ) (m : ℕ) (k : ℝ) (Q : (Fin 3 → Fin 2) → Prop) [DecidablePred Q]
    (hp : ∀ x : Fin 3 → Fin 2, (exampleLaw j).prob x = if Q x then c0 else 0)
    (hv : IsLaw (exampleLaw j).prob)
    (s : Finset (Fin 3)) (hc : Real.logb 2 (c0 * m) = -k)
    (hdec : ∀ a : (i : {i : Fin 3 // i ∈ s}) → Fin 2,
      (Finset.univ.filter (fun x : Fin 3 → Fin 2 => (∀ i : {i : Fin 3 // i ∈ s}, x i.val = a i) ∧ Q x)).card = 0 ∨
      (Finset.univ.filter (fun x : Fin 3 → Fin 2 => (∀ i : {i : Fin 3 // i ∈ s}, x i.val = a i) ∧ Q x)).card = m) :
    cH (exampleLaw j) s = k := by
  refine X7G5_cH_val _ hv s (c0 * m) k hc fun a => ?_
  rw [X7G5_marg3 j c0 Q hp s a]
  rcases hdec a with h | h
  · left; rw [h]; simp
  · right; rw [h]

theorem X7G5_lawsum (j : Fin 5) (c0 : ℝ) (Q : (Fin 3 → Fin 2) → Prop) [DecidablePred Q]
    (hp : ∀ x : Fin 3 → Fin 2, (exampleLaw j).prob x = if Q x then c0 else 0) (hc : 0 ≤ c0)
    (hcard : c0 * (Finset.univ.filter Q).card = 1) : IsValidClassicalData (exampleLaw j) := by
  have hs : ∑ x : ClassicalBasis (exampleLaw j).dims, (exampleLaw j).prob x =
      ∑ x : Fin 3 → Fin 2, (if Q x then c0 else 0) := Finset.sum_congr rfl (fun x _ => hp x)
  refine ⟨fun i => by simp [exampleLaw], fun x => by rw [hp x]; split_ifs <;> simp [hc], hs.trans ?_⟩
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact hcard

theorem X7G5_lb2 : Real.logb 2 (1/2 * (1:ℕ)) = -1 := by
  simp [Real.logb_inv]
theorem X7G5_lb1 : Real.logb 2 (1/2 * (2:ℕ)) = -0 := by norm_num
theorem X7G5_lb4 : Real.logb 2 (1/4 * (1:ℕ)) = -2 := by
  rw [show (1/4 * ((1:ℕ):ℝ)) = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.logb_pow, Real.logb_inv]; simp
theorem X7G5_lb42 : Real.logb 2 (1/4 * (2:ℕ)) = -1 := by
  rw [show (1/4 * ((2:ℕ):ℝ)) = (2:ℝ)⁻¹ by norm_num, Real.logb_inv]; simp

theorem X7G5_L0 : IsValidClassicalData (exampleLaw 0) ∧ ∀ i : Fin 5, fiveValues (exampleLaw 0) i = fiveTable 0 i := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 0).prob x = if (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) x then 1/2 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := X7G5_lawsum 0 (1/2) (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp (by norm_num) (by rw [show (Finset.univ.filter (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0)).card = 2 by decide]; norm_num)
  have e0 := X7G5_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {0} X7G5_lb2 (by decide)
  have e1 := X7G5_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {1} X7G5_lb2 (by decide)
  have e2 := X7G5_val3 0 (1/2) 2 0 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {2} X7G5_lb1 (by decide)
  have e01 := X7G5_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {0,1} X7G5_lb2 (by decide)
  have e02 := X7G5_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {0,2} X7G5_lb2 (by decide)
  have e12 := X7G5_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {1,2} X7G5_lb2 (by decide)
  have eU := X7G5_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 Finset.univ X7G5_lb2 (by decide)
  refine ⟨hv, fun i => ?_⟩
  rw [X7G5_five _ hv  1 1 0 1 1 1 1 e0 e1 e2 e01 e02 e12 eU]
  fin_cases i <;> simp [fiveTable] <;> norm_num

theorem X7G5_L1 : IsValidClassicalData (exampleLaw 1) ∧ ∀ i : Fin 5, fiveValues (exampleLaw 1) i = fiveTable 1 i := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 1).prob x = if (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) x then 1/2 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := X7G5_lawsum 1 (1/2) (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp (by norm_num) (by rw [show (Finset.univ.filter (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0)).card = 2 by decide]; norm_num)
  have e0 := X7G5_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {0} X7G5_lb2 (by decide)
  have e1 := X7G5_val3 1 (1/2) 2 0 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {1} X7G5_lb1 (by decide)
  have e2 := X7G5_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {2} X7G5_lb2 (by decide)
  have e01 := X7G5_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {0,1} X7G5_lb2 (by decide)
  have e02 := X7G5_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {0,2} X7G5_lb2 (by decide)
  have e12 := X7G5_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {1,2} X7G5_lb2 (by decide)
  have eU := X7G5_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 Finset.univ X7G5_lb2 (by decide)
  refine ⟨hv, fun i => ?_⟩
  rw [X7G5_five _ hv  1 0 1 1 1 1 1 e0 e1 e2 e01 e02 e12 eU]
  fin_cases i <;> simp [fiveTable] <;> norm_num

theorem X7G5_L2 : IsValidClassicalData (exampleLaw 2) ∧ ∀ i : Fin 5, fiveValues (exampleLaw 2) i = fiveTable 2 i := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 2).prob x = if (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) x then 1/2 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := X7G5_lawsum 2 (1/2) (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp (by norm_num) (by rw [show (Finset.univ.filter (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0)).card = 2 by decide]; norm_num)
  have e0 := X7G5_val3 2 (1/2) 2 0 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {0} X7G5_lb1 (by decide)
  have e1 := X7G5_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {1} X7G5_lb2 (by decide)
  have e2 := X7G5_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {2} X7G5_lb2 (by decide)
  have e01 := X7G5_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {0,1} X7G5_lb2 (by decide)
  have e02 := X7G5_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {0,2} X7G5_lb2 (by decide)
  have e12 := X7G5_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {1,2} X7G5_lb2 (by decide)
  have eU := X7G5_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 Finset.univ X7G5_lb2 (by decide)
  refine ⟨hv, fun i => ?_⟩
  rw [X7G5_five _ hv  0 1 1 1 1 1 1 e0 e1 e2 e01 e02 e12 eU]
  fin_cases i <;> simp [fiveTable] <;> norm_num

theorem X7G5_L3 : IsValidClassicalData (exampleLaw 3) ∧ ∀ i : Fin 5, fiveValues (exampleLaw 3) i = fiveTable 3 i := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 3).prob x = if (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) x then 1/2 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := X7G5_lawsum 3 (1/2) (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp (by norm_num) (by rw [show (Finset.univ.filter (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2)).card = 2 by decide]; norm_num)
  have e0 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {0} X7G5_lb2 (by decide)
  have e1 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {1} X7G5_lb2 (by decide)
  have e2 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {2} X7G5_lb2 (by decide)
  have e01 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {0,1} X7G5_lb2 (by decide)
  have e02 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {0,2} X7G5_lb2 (by decide)
  have e12 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {1,2} X7G5_lb2 (by decide)
  have eU := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 Finset.univ X7G5_lb2 (by decide)
  refine ⟨hv, fun i => ?_⟩
  rw [X7G5_five _ hv  1 1 1 1 1 1 1 e0 e1 e2 e01 e02 e12 eU]
  fin_cases i <;> simp [fiveTable] <;> norm_num

theorem X7G5_L4 : IsValidClassicalData (exampleLaw 4) ∧ ∀ i : Fin 5, fiveValues (exampleLaw 4) i = fiveTable 4 i := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 4).prob x = if (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) x then 1/4 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := X7G5_lawsum 4 (1/4) (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp (by norm_num) (by rw [show (Finset.univ.filter (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0)).card = 4 by decide]; norm_num)
  have e0 := X7G5_val3 4 (1/4) 2 1 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {0} X7G5_lb42 (by decide)
  have e1 := X7G5_val3 4 (1/4) 2 1 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {1} X7G5_lb42 (by decide)
  have e2 := X7G5_val3 4 (1/4) 2 1 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {2} X7G5_lb42 (by decide)
  have e01 := X7G5_val3 4 (1/4) 1 2 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {0,1} X7G5_lb4 (by decide)
  have e02 := X7G5_val3 4 (1/4) 1 2 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {0,2} X7G5_lb4 (by decide)
  have e12 := X7G5_val3 4 (1/4) 1 2 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {1,2} X7G5_lb4 (by decide)
  have eU := X7G5_val3 4 (1/4) 1 2 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 Finset.univ X7G5_lb4 (by decide)
  refine ⟨hv, fun i => ?_⟩
  rw [X7G5_five _ hv  1 1 1 2 2 2 2 e0 e1 e2 e01 e02 e12 eU]
  fin_cases i <;> simp [fiveTable] <;> norm_num



theorem X7G5_c3 : cH (exampleLaw 3) {0} = 1 ∧ cH (exampleLaw 3) {1} = 1 ∧ cH (exampleLaw 3) {2} = 1 ∧
    cH (exampleLaw 3) {0,1} = 1 ∧ cH (exampleLaw 3) {0,2} = 1 ∧ cH (exampleLaw 3) {1,2} = 1 ∧
    cH (exampleLaw 3) ∅ = 0 := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 3).prob x = if (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) x then 1/2 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := X7G5_L3.1
  have e0 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {0} X7G5_lb2 (by decide)
  have e1 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {1} X7G5_lb2 (by decide)
  have e2 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {2} X7G5_lb2 (by decide)
  have e01 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {0,1} X7G5_lb2 (by decide)
  have e02 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {0,2} X7G5_lb2 (by decide)
  have e12 := X7G5_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {1,2} X7G5_lb2 (by decide)
  exact ⟨e0, e1, e2, e01, e02, e12, X7G5_cH_empty _ hv⟩

theorem X7G5_vals : cValue .dual (exampleLaw 3) = 1 ∧ cValue .total (exampleLaw 3) = 2 ∧
    cValue .dual (exampleLaw 4) = 2 ∧ cValue .total (exampleLaw 4) = 1 := by
  have a := X7G5_L3.2 3
  have b := X7G5_L3.2 4
  have c := X7G5_L4.2 3
  have d := X7G5_L4.2 4
  simp [fiveValues, fiveTable] at a b c d
  exact ⟨a, b, c, d⟩

section X7GHsec
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq

def X7GH_C (x : Fin 3 → Fin 2) : Prop := (∀ i, x i = 0) ∨ (∀ i, x i = 1)

lemma X7GH_ghz (x : Fin 3 → Fin 2) :
    ghzVector 3 x = if X7GH_C x then ((Real.sqrt 2 : ℂ)⁻¹) else 0 := by
  unfold ghzVector X7GH_C; simp only [WithLp.ofLp_toLp]; congr 1

lemma X7GH_sum (isX : Bool) (a : Fin 3 → Fin 2) :
    ∑ x : Fin 3 → Fin 2, (∏ i, conj (qubitBasis isX (a i) (x i))) * ghzVector 3 x =
      ((∏ i, conj (qubitBasis isX (a i) 0)) + (∏ i, conj (qubitBasis isX (a i) 1))) *
        (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [Finset.sum_eq_add_of_mem (fun _ => 0) (fun _ => 1) (Finset.mem_univ _) (Finset.mem_univ _)
    (by intro h; have := congrFun h 0; simp at this)]
  · rw [X7GH_ghz, X7GH_ghz, if_pos (show X7GH_C (fun _ => 0) from Or.inl fun _ => rfl),
      if_pos (show X7GH_C (fun _ => 1) from Or.inr fun _ => rfl), add_mul]
  · intro c _ hc
    rw [X7GH_ghz, if_neg, mul_zero]
    rintro (h | h)
    · exact hc.1 (funext h)
    · exact hc.2 (funext h)

lemma X7GH_s2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma X7GH_meas0 : ghzMeasurement false = exampleLaw 3 := by
  unfold ghzMeasurement exampleLaw
  congr 1
  funext a
  rw [X7GH_sum]
  have ha : a = ![a 0, a 1, a 2] := by funext i; fin_cases i <;> rfl
  rw [ha]
  generalize a 0 = u; generalize a 1 = v; generalize a 2 = w
  fin_cases u <;> fin_cases v <;> fin_cases w <;>
    simp [qubitBasis, Fin.prod_univ_three, Complex.normSq_apply] <;> norm_num

lemma X7GH_qbT (a x : Fin 2) : conj (qubitBasis true a x) =
    (((if a = 1 ∧ x = 1 then -1 else 1 : ℝ) * (Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  show conj ((if a = 1 ∧ x = 1 then -1 else 1) / (Real.sqrt 2 : ℂ)) = _
  split_ifs <;> simp [map_div₀, Complex.conj_ofReal] <;> ring

lemma X7GH_sumT (a : Fin 3 → Fin 2) :
    ∑ x : Fin 3 → Fin 2, (∏ i, conj (qubitBasis true (a i) (x i))) * ghzVector 3 x =
      ((((∏ i, (if a i = 1 ∧ (0:Fin 2) = 1 then -1 else 1 : ℝ)) +
        (∏ i, (if a i = 1 ∧ (1:Fin 2) = 1 then -1 else 1 : ℝ))) * ((Real.sqrt 2)⁻¹) ^ 4 : ℝ) : ℂ) := by
  rw [X7GH_sum]
  simp only [X7GH_qbT, Fin.prod_univ_three]
  push_cast
  ring

lemma X7GH_meas1 : ghzMeasurement true = exampleLaw 4 := by
  unfold ghzMeasurement exampleLaw
  congr 1
  funext a
  rw [X7GH_sumT, Complex.normSq_ofReal]
  have h4 : ((Real.sqrt 2)⁻¹) ^ 4 = (1/4 : ℝ) := by
    rw [inv_pow, show (4:ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num
  rw [h4]
  have ha : a = ![a 0, a 1, a 2] := by funext i; fin_cases i <;> rfl
  rw [ha]
  generalize a 0 = u; generalize a 1 = v; generalize a 2 = w
  fin_cases u <;> fin_cases v <;> fin_cases w <;>
    simp [Fin.prod_univ_three] <;> norm_num

open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal SubBasis)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms

lemma X7GH_Ciff (x : Fin 3 → Fin 2) : X7GH_C x ↔ (x 0 = x 1 ∧ x 1 = x 2) := by
  unfold X7GH_C
  constructor
  · rintro (h | h) <;> simp [h]
  · rintro ⟨h1, h2⟩
    rcases (show x 0 = 0 ∨ x 0 = 1 by omega) with h | h
    · left; intro i; fin_cases i <;> simp_all
    · right; intro i; fin_cases i <;> simp_all

lemma X7GH_prod (x y : Fin 3 → Fin 2) :
    ghzVector 3 x * (starRingEnd ℂ) (ghzVector 3 y) = if X7GH_C x ∧ X7GH_C y then (1/2 : ℂ) else 0 := by
  rw [X7GH_ghz, X7GH_ghz]
  split_ifs with h1 h2 h3 <;> simp_all
  rw [X7GH_s2]; norm_num

lemma X7GH_law3 (x : Fin 3 → Fin 2) :
    (exampleLaw 3).prob x = if X7GH_C x then 1/2 else 0 := by
  rw [show (exampleLaw 3).prob x = if x 0 = x 1 ∧ x 1 = x 2 then 1/2 else 0 by
    unfold exampleLaw; dsimp only; split_ifs <;> simp_all]
  simp only [X7GH_Ciff]

def X7GH_d (s : Finset (Fin 3)) (a : SubBasis (fun _ : Fin 3 => Fin 2) s) : ℝ :=
  ∑ x : Fin 3 → Fin 2, if (∀ i : {i // i ∈ s}, x i.val = a i) then
    (if X7GH_C x then (1/2:ℝ) else 0) else 0

lemma X7GH_cH (s : Finset (Fin 3)) : cH (exampleLaw 3) s = shannon (X7GH_d s) := by
  unfold cH shannon
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun a _ => ?_))
  have : lawMarginal (exampleLaw 3) s a = X7GH_d s a := by
    unfold lawMarginal X7GH_d
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hx := X7GH_law3 x
    rcases em (∀ i : {i // i ∈ s}, x i.val = a i) with h | h
    · rw [if_pos h]; exact hx.trans (if_pos h).symm
    · rw [if_neg h]; exact (if_neg h).symm
  rw [this]

lemma X7GH_diag_entry (s : Finset (Fin 3)) (hs : s ≠ Finset.univ)
    (a b : SubBasis (fun _ : Fin 3 => Fin 2) s) :
    registerMarginal (trivialExtension (pureDensity (ghzVector 3))) s (a, ()) (b, ()) =
      if a = b then ((X7GH_d s a : ℝ) : ℂ) else 0 := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ s := by
    by_contra h; push_neg at h; exact hs (Finset.eq_univ_of_forall h)
  simp only [registerMarginal, trivialExtension, pureDensity, Matrix.of_apply]
  have inner : ∀ x : Fin 3 → Fin 2, (∑ y : Fin 3 → Fin 2,
      if (∀ i (hi : i ∈ s), x i = a ⟨i, hi⟩ ∧ y i = b ⟨i, hi⟩) ∧ (∀ i, i ∉ s → x i = y i)
      then ghzVector 3 x * (starRingEnd ℂ) (ghzVector 3 y) else 0) =
      if (∀ i (hi : i ∈ s), x i = a ⟨i, hi⟩ ∧ x i = b ⟨i, hi⟩) ∧ X7GH_C x then (1/2 : ℂ) else 0 := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [X7GH_prod]
      by_cases h1 : ∀ i (hi : i ∈ s), x i = a ⟨i, hi⟩ ∧ x i = b ⟨i, hi⟩ <;>
        by_cases h2 : X7GH_C x <;> simp [h1, h2]
    · intro y _ hyx
      split_ifs with h
      · rw [X7GH_prod, if_neg]
        rintro ⟨hx, hy⟩
        apply hyx
        have hxy := h.2 j hj
        funext i
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · rw [hx, hy]
        · exfalso; rw [hx j, hy j] at hxy; exact absurd hxy (by decide)
        · exfalso; rw [hx j, hy j] at hxy; exact absurd hxy (by decide)
        · rw [hx, hy]
      · rfl
    · simp
  have e := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3 → Fin 2))) rfl
    (fun x _ => inner x)
  refine (Eq.trans ?_ e).trans ?_
  · congr 1; funext x; congr 1; funext y; congr 1
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    unfold X7GH_d
    push_cast
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h1 : ∀ i : {i : Fin 3 // i ∈ s}, x i.val = a i
    · rw [if_pos h1]
      by_cases h2 : X7GH_C x
      · rw [if_pos ⟨fun i hi => ⟨h1 ⟨i, hi⟩, h1 ⟨i, hi⟩⟩, h2⟩, if_pos h2]; push_cast; ring
      · rw [if_neg (fun h => h2 h.2), if_neg h2]; simp
    · rw [if_neg h1, if_neg]
      · exact Complex.ofReal_zero.symm
      intro h; exact h1 (fun i => (h.1 i.1 i.2).1)
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    intro h; apply hab; funext i
    exact (h.1 i.1 i.2).1.symm.trans (h.1 i.1 i.2).2

lemma X7GH_diag (s : Finset (Fin 3)) (hs : s ≠ Finset.univ) :
    registerMarginal (trivialExtension (pureDensity (ghzVector 3))) s =
      Matrix.diagonal (fun a : SubBasis (fun _ : Fin 3 => Fin 2) s × Unit =>
        ((X7GH_d s a.1 : ℝ) : ℂ)) := by
  ext ⟨a, u⟩ ⟨b, v⟩
  cases u; cases v
  rw [X7GH_diag_entry s hs a b, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, if_neg (fun e => h (congrArg Prod.fst e))]
lemma X7GH_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma X7GH_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma X7GH_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := X7GH_diag_herm d
  rw [X7GH_cfc_trace hD]
  have h1 := hD.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma X7GH_vn_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [X7GH_trace_cfc_diag]
  simp

lemma X7GH_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

lemma X7GH_ent_proper (s : Finset (Fin 3)) (hs : s ≠ Finset.univ) :
    entropyAt (trivialExtension (pureDensity (ghzVector 3))) s = cH (exampleLaw 3) s := by
  unfold entropyAt
  rw [X7GH_diag s hs]
  have hv := X7GH_vn_diag (fun a : SubBasis (fun _ : Fin 3 => Fin 2) s × Unit => X7GH_d s a.1)
  refine (Eq.trans ?_ hv).trans ?_
  · congr 1
  rw [X7GH_cH]
  unfold shannon
  congr 1
  rw [Fintype.sum_prod_type]
  simp

def X7GH_phi (a : SubBasis (fun _ : Fin 3 => Fin 2) Finset.univ) : ℂ :=
  ghzVector 3 (fun i => a ⟨i, Finset.mem_univ i⟩)

lemma X7GH_univ_entry (a b : SubBasis (fun _ : Fin 3 => Fin 2) Finset.univ) :
    registerMarginal (trivialExtension (pureDensity (ghzVector 3))) Finset.univ (a, ()) (b, ()) =
      X7GH_phi a * (starRingEnd ℂ) (X7GH_phi b) := by
  simp only [registerMarginal, trivialExtension, pureDensity, Matrix.of_apply]
  rw [Finset.sum_eq_single (fun i => a ⟨i, Finset.mem_univ i⟩)]
  · rw [Finset.sum_eq_single (fun i => b ⟨i, Finset.mem_univ i⟩)]
    · rw [if_pos ⟨fun i hi => ⟨rfl, rfl⟩, fun i hi => absurd (Finset.mem_univ i) hi⟩]; rfl
    · intro y _ hy
      rw [if_neg]
      intro h; apply hy; funext i; exact (h.1 i (Finset.mem_univ i)).2
    · simp
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    intro h; apply hx; funext i; exact (h.1 i (Finset.mem_univ i)).1
  · simp

def X7GH_e : SubBasis (fun _ : Fin 3 => Fin 2) Finset.univ ≃ (Fin 3 → Fin 2) where
  toFun a := fun i => a ⟨i, Finset.mem_univ i⟩
  invFun x := fun i => x i.1
  left_inv a := rfl
  right_inv x := rfl

lemma X7GH_normsum :
    ∑ a : SubBasis (fun _ : Fin 3 => Fin 2) Finset.univ,
      X7GH_phi a * (starRingEnd ℂ) (X7GH_phi a) = 1 := by
  rw [show (∑ a : SubBasis (fun _ : Fin 3 => Fin 2) Finset.univ,
      X7GH_phi a * (starRingEnd ℂ) (X7GH_phi a)) =
      ∑ x : Fin 3 → Fin 2, ghzVector 3 x * (starRingEnd ℂ) (ghzVector 3 x) from
    Fintype.sum_equiv X7GH_e _ _ (fun a => rfl)]
  simp_rw [X7GH_prod, and_self]
  rw [Finset.sum_eq_add_of_mem (fun _ => 0) (fun _ => 1) (Finset.mem_univ _) (Finset.mem_univ _)
    (by intro h; have := congrFun h 0; simp at this)]
  · rw [if_pos (show X7GH_C (fun _ => 0) from Or.inl fun _ => rfl),
      if_pos (show X7GH_C (fun _ => 1) from Or.inr fun _ => rfl)]; norm_num
  · intro c _ hc
    rw [if_neg]
    rintro (h | h)
    · exact hc.1 (funext h)
    · exact hc.2 (funext h)

lemma X7GH_ent_univ :
    entropyAt (trivialExtension (pureDensity (ghzVector 3))) Finset.univ = 0 := by
  unfold entropyAt
  set M := registerMarginal (trivialExtension (pureDensity (ghzVector 3))) Finset.univ with hM
  have hent : ∀ p q, M p q = X7GH_phi p.1 * (starRingEnd ℂ) (X7GH_phi q.1) := by
    rintro ⟨a, u⟩ ⟨b, v⟩; cases u; cases v; exact X7GH_univ_entry a b
  have hMM : M * M = M := by
    ext p q
    rw [Matrix.mul_apply]
    simp_rw [hent]
    have : ∑ r : SubBasis (fun _ : Fin 3 => Fin 2) Finset.univ × Unit,
        X7GH_phi p.1 * (starRingEnd ℂ) (X7GH_phi r.1) *
          (X7GH_phi r.1 * (starRingEnd ℂ) (X7GH_phi q.1)) =
        X7GH_phi p.1 * (starRingEnd ℂ) (X7GH_phi q.1) *
          ∑ a : SubBasis (fun _ : Fin 3 => Fin 2) Finset.univ,
            X7GH_phi a * (starRingEnd ℂ) (X7GH_phi a) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [Finset.univ_unique, Finset.sum_singleton]
      ring
    rw [this, X7GH_normsum, mul_one]
  have htr : M.trace = 1 := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    simp only [Matrix.diag, hent, Finset.univ_unique, Finset.sum_singleton]
    exact X7GH_normsum
  have hherm : M.IsHermitian := by
    ext p q
    rw [Matrix.conjTranspose_apply, hent, hent]
    simp [mul_comm]
  have hpow : ∀ k : ℕ, (M ^ (k + 1)).trace = ((1 : Matrix Unit Unit ℂ) ^ (k + 1)).trace := by
    intro k
    have : M ^ (k + 1) = M := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ih, hMM]
    rw [this, htr, one_pow]; simp
  have h := X7GH_trace_cfc_eq M (1 : Matrix Unit Unit ℂ) hherm Matrix.isHermitian_one
    (fun x : ℝ => x * Real.logb 2 x) (by simp) hpow
  have h1 : (1 : Matrix Unit Unit ℂ) = Matrix.diagonal (fun i => (((fun _ => 1) : Unit → ℝ) i : ℂ)) := by
    simp
  have h0 : -(cfc (fun x : ℝ => x * Real.logb 2 x) M).trace.re = 0 := by
    rw [h, h1, X7GH_trace_cfc_diag]; simp
  unfold vnEntropy
  convert h0

lemma X7GH_info : info .dual (pureDensity (ghzVector 3)) (singleParties 3) ∅ = 3 ∧
    info .total (pureDensity (ghzVector 3)) (singleParties 3) ∅ = 3 := by
  obtain ⟨c0, c1, c2, c01, c02, c12, cE⟩ := X7G5_c3
  have E : ∀ s : Finset (Fin 3), s ≠ Finset.univ →
      entropyAt (trivialExtension (pureDensity (ghzVector 3))) s = cH (exampleLaw 3) s :=
    X7GH_ent_proper
  have hs : singleParties 3 = fun i => ({i} : Finset (Fin 3)) := rfl
  have r0 : (Finset.univ.erase 0 : Finset (Fin 3)) = {1, 2} := by ext j; fin_cases j <;> simp
  have r1 : (Finset.univ.erase 1 : Finset (Fin 3)) = {0, 2} := by ext j; fin_cases j <;> simp
  have r2 : (Finset.univ.erase 2 : Finset (Fin 3)) = {0, 1} := by ext j; fin_cases j <;> simp
  have n0 : ({0} : Finset (Fin 3)) ≠ Finset.univ := fun h => by
    have := Finset.mem_univ (1 : Fin 3); rw [← h] at this; simp at this
  have n1 : ({1} : Finset (Fin 3)) ≠ Finset.univ := fun h => by
    have := Finset.mem_univ (0 : Fin 3); rw [← h] at this; simp at this
  have n2 : ({2} : Finset (Fin 3)) ≠ Finset.univ := fun h => by
    have := Finset.mem_univ (0 : Fin 3); rw [← h] at this; simp at this
  have n12 : ({1, 2} : Finset (Fin 3)) ≠ Finset.univ := fun h => by
    have := Finset.mem_univ (0 : Fin 3); rw [← h] at this; simp at this
  have n02 : ({0, 2} : Finset (Fin 3)) ≠ Finset.univ := fun h => by
    have := Finset.mem_univ (1 : Fin 3); rw [← h] at this; simp at this
  have n01 : ({0, 1} : Finset (Fin 3)) ≠ Finset.univ := fun h => by
    have := Finset.mem_univ (2 : Fin 3); rw [← h] at this; simp at this
  have nE : (∅ : Finset (Fin 3)) ≠ Finset.univ := fun h => by
    have := Finset.mem_univ (0 : Fin 3); rw [← h] at this; simp at this
  constructor
  · unfold info QAlgorithms.Papers.Independent.Claimed50.P33.conditionalMultipartiteInformation
    simp only [hs, allParties, Finset.biUnion_singleton_eq_self, Finset.union_empty,
      Fin.sum_univ_three, r0, r1, r2]
    rw [E _ n12, E _ n02, E _ n01, X7GH_ent_univ, E _ nE, c12, c02, c01, cE]
    norm_num
  · unfold info QAlgorithms.Papers.Independent.Claimed50.P33.conditionalMultipartiteInformation
    simp only [hs, allParties, Finset.biUnion_singleton_eq_self, Finset.union_empty,
      Fin.sum_univ_three]
    rw [E _ n0, E _ n1, E _ n2, X7GH_ent_univ, E _ nE, c0, c1, c2, cE]
    norm_num

end X7GHsec

section X7GHfinal
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)
open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P37 in
theorem solution :
    ghzMeasurement false = exampleLaw 3 ∧ ghzMeasurement true = exampleLaw 4 ∧
    info .dual (pureDensity (ghzVector 3)) (singleParties 3) ∅ = 3 ∧
    info .total (pureDensity (ghzVector 3)) (singleParties 3) ∅ = 3 ∧
    cValue .dual (exampleLaw 3) = 1 ∧ cValue .total (exampleLaw 3) = 2 ∧
    cValue .dual (exampleLaw 4) = 2 ∧ cValue .total (exampleLaw 4) = 1 ∧
    cValue .dual (exampleLaw 3) + cValue .total (exampleLaw 3) =
      cValue .dual (exampleLaw 4) + cValue .total (exampleLaw 4) ∧
    cValue .dual (exampleLaw 3) + cValue .total (exampleLaw 3) =
      (info .dual (pureDensity (ghzVector 3)) (singleParties 3) ∅ +
       info .total (pureDensity (ghzVector 3)) (singleParties 3) ∅) / 2 := by
  obtain ⟨a, b, c, d⟩ := X7G5_vals
  obtain ⟨i1, i2⟩ := X7GH_info
  refine ⟨X7GH_meas0, X7GH_meas1, i1, i2, a, b, c, d, ?_, ?_⟩
  · rw [a, b, c, d]; norm_num
  · rw [a, b, i1, i2]; norm_num

end X7GHfinal
