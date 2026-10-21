-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P37.tripartiteMonotoneCone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:04:30.649629+00:00
-- url     : https://prove2.me/submissions/4def68f0-8261-41d6-8109-373f0e0df685

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37
noncomputable section
open QAlgorithms.Papers.Independent.Renew46.P37
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Claimed50.P33 (InformationKind singleParties allParties)

theorem g64e_shannon_const {Y : Type} [Fintype Y] (q : Y → ℝ) (c k : ℝ)
    (hc : Real.logb 2 c = -k) (h : ∀ y, q y = 0 ∨ q y = c) (hs : ∑ y, q y = 1) :
    shannon q = k := by
  unfold shannon
  have : ∀ y, q y * Real.logb 2 (q y) = q y * (-k) := by
    intro y; rcases h y with h1 | h1 <;> rw [h1]; simp; rw [hc]
  simp only [this, ← Finset.sum_mul, hs]; ring

theorem g64e_marg_sum {n : ℕ} (p : CData n) (s : Finset (Fin n)) :
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

theorem g64e_cH_val {n : ℕ} (p : CData n) (hp : IsLaw p.prob) (s : Finset (Fin n)) (c k : ℝ)
    (hc : Real.logb 2 c = -k) (h : ∀ a, lawMarginal p s a = 0 ∨ lawMarginal p s a = c) :
    cH p s = k :=
  g64e_shannon_const _ c k hc h (by rw [g64e_marg_sum, hp.2])

theorem g64e_marg {n : ℕ} (p : CData n) (c0 : ℝ) (Q : ClassicalBasis p.dims → Prop)
    [DecidablePred Q] (hp : ∀ x, p.prob x = if Q x then c0 else 0) (s : Finset (Fin n))
    (a : (i : {i : Fin n // i ∈ s}) → Fin (p.dims i.val)) :
    lawMarginal p s a = c0 * (Finset.univ.filter (fun x : ClassicalBasis p.dims =>
      (∀ i : {i : Fin n // i ∈ s}, x i.val = a i) ∧ Q x)).card := by
  unfold lawMarginal
  simp only [hp]
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h1 : ∀ i : {i : Fin n // i ∈ s}, x i.val = a i <;> by_cases h2 : Q x <;> simp [h1, h2]

theorem g64e_cH_empty {n : ℕ} (p : CData n) (hp : IsValidClassicalData p) :
    cH p ∅ = 0 := by
  have := g64e_cH_val p hp.2 ∅ 1 0 (by simp) (fun a => Or.inr (by
    unfold lawMarginal
    rw [← hp.2.2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [if_pos]
    intro i; exact absurd i.2 (Finset.notMem_empty _)))
  exact this

theorem g64e_dual {n : ℕ} (p : CData n) :
    cValue .dual p = (∑ i, cH p (Finset.univ.erase i)) - (n - 1 : ℕ) * cH p Finset.univ := by
  have hs : QAlgorithms.Papers.Independent.Claimed50.P33.singleParties n =
      fun i => ({i} : Finset (Fin n)) := rfl
  simp only [cValue, cInfo, QAlgorithms.Papers.Independent.Claimed50.P33.allParties, hs,
    Finset.biUnion_singleton_eq_self]

theorem g64e_total {n : ℕ} (p : CData n) :
    cValue .total p = (∑ i, cH p {i}) - cH p Finset.univ := by
  have hs : QAlgorithms.Papers.Independent.Claimed50.P33.singleParties n =
      fun i => ({i} : Finset (Fin n)) := rfl
  simp only [cValue, cInfo, QAlgorithms.Papers.Independent.Claimed50.P33.allParties, hs,
    Finset.biUnion_singleton_eq_self]


theorem g64e_sum {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .dual p + cValue .total p =
      ∑ i, lawCMI p {i} (Finset.univ.erase i) ∅ := by
  rw [g64e_dual, g64e_total]
  have hu : ∀ i : Fin n, {i} ∪ Finset.univ.erase i ∪ ∅ = Finset.univ := by
    intro i; ext j; by_cases h : j = i <;> simp [h]
  simp only [lawCMI, hu, Finset.union_empty, g64e_cH_empty p hp, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [this]; ring

def g64e_G {n : ℕ} (p : CData n) (k : ℕ) : ℝ := cH p (Finset.univ.filter fun j : Fin n => j.val < k)

theorem g64e_tele {m : ℕ} (p : CData (m+1)) (hp : IsValidClassicalData p) :
    ∑ i : Fin m, (g64e_G p (i.val + 1) - g64e_G p i.val) =
      cH p (Finset.univ.erase (Fin.last m)) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => g64e_G p (k + 1) - g64e_G p k) m,
    Finset.sum_range_sub]
  have h0 : g64e_G p 0 = 0 := by
    unfold g64e_G; simpa using g64e_cH_empty p hp
  rw [h0, sub_zero]; unfold g64e_G; congr 1; ext j
  simp [Fin.ext_iff, Fin.lt_def] <;> omega

theorem g64e_S3 {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .dual p = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n),
      lawCMI p {i} (later i) (earlier i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [g64e_dual, Finset.sum_filter, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
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
  have := g64e_tele p hp
  simp only [g64e_G] at this
  have h2 : ∑ i : Fin m, (cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1) +
      cH p (Finset.univ.erase i.castSucc) -
      cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val) - cH p Finset.univ) =
      (∑ i : Fin m, (cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1) -
      cH p (Finset.univ.filter fun j : Fin (m+1) => j.val < i.val))) +
      ∑ i : Fin m, cH p (Finset.univ.erase i.castSucc) - m * cH p Finset.univ := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]; ring
  linarith [h2, this]

theorem g64e_T1 {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .total p = ∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < i.val),
      lawCMI p (earlier i) {i} ∅ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [g64e_total, Finset.sum_filter,
    Fin.sum_univ_succ (f := fun a => if 0 < a.val then lawCMI p (earlier a) {a} ∅ else 0),
    Fin.sum_univ_succ (f := fun i => cH p {i})]
  simp only [Fin.val_zero, lt_self_iff_false, if_false, zero_add, Fin.val_succ,
    Nat.succ_pos, if_true, lawCMI, Finset.union_empty, g64e_cH_empty p hp, sub_zero]
  have e1 : ∀ i : Fin m, earlier i.succ = Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1 := by
    intro i; ext j; simp [earlier]
  have e2 : ∀ i : Fin m, earlier i.succ ∪ {i.succ} =
      Finset.univ.filter fun j : Fin (m+1) => j.val < i.val + 1 + 1 := by
    intro i; ext j; simp [earlier, Fin.ext_iff] <;> omega
  simp only [e2]
  simp only [e1]
  have := Finset.sum_range_sub (fun k => - g64e_G p (k + 1)) m
  rw [← Fin.sum_univ_eq_sum_range (fun k => - g64e_G p (k + 1 + 1) - - g64e_G p (k + 1)) m] at this
  simp only [g64e_G] at this
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

theorem g64e_T2 {n : ℕ} (hn : 3 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
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
  simp only [cInfo, lawCMI, hL, hR, hLR, hA, hsum, Finset.union_empty, g64e_cH_empty p hp]
  rw [g64e_total, Fin.sum_univ_castSucc]; ring

theorem g64e_S4 {n : ℕ} (hn : 3 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
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
  rw [g64e_dual, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  push_cast
  have h1 : ((k + 3 - 1 - 1 : ℕ) : ℝ) = k + 1 := by
    rw [show k + 3 - 1 - 1 = k + 1 by omega]; push_cast; ring
  have h2 : ((k + 3 - 1 : ℕ) : ℝ) = k + 2 := by
    rw [show k + 3 - 1 = k + 2 by omega]; push_cast; ring
  ring

theorem g64e_five (p : CData 3) (hp : IsValidClassicalData p) (h0 h1 h2 h01 h02 h12 hU : ℝ)
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
  rw [g64e_dual, g64e_total, Fin.sum_univ_three, Fin.sum_univ_three, s1, s2, s3, r0, r1, r2]
  simp only [Finset.union_empty, g64e_cH_empty p hp, e0, e1, e2, e01, e02, e12, eU]
  ext i; fin_cases i <;> simp <;> norm_num <;> ring

theorem g64e_marg3 (j : Fin 5) (c0 : ℝ) (Q : (Fin 3 → Fin 2) → Prop) [DecidablePred Q]
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

theorem g64e_val3 (j : Fin 5) (c0 : ℝ) (m : ℕ) (k : ℝ) (Q : (Fin 3 → Fin 2) → Prop) [DecidablePred Q]
    (hp : ∀ x : Fin 3 → Fin 2, (exampleLaw j).prob x = if Q x then c0 else 0)
    (hv : IsLaw (exampleLaw j).prob)
    (s : Finset (Fin 3)) (hc : Real.logb 2 (c0 * m) = -k)
    (hdec : ∀ a : (i : {i : Fin 3 // i ∈ s}) → Fin 2,
      (Finset.univ.filter (fun x : Fin 3 → Fin 2 => (∀ i : {i : Fin 3 // i ∈ s}, x i.val = a i) ∧ Q x)).card = 0 ∨
      (Finset.univ.filter (fun x : Fin 3 → Fin 2 => (∀ i : {i : Fin 3 // i ∈ s}, x i.val = a i) ∧ Q x)).card = m) :
    cH (exampleLaw j) s = k := by
  refine g64e_cH_val _ hv s (c0 * m) k hc fun a => ?_
  rw [g64e_marg3 j c0 Q hp s a]
  rcases hdec a with h | h
  · left; rw [h]; simp
  · right; rw [h]

theorem g64e_lawsum (j : Fin 5) (c0 : ℝ) (Q : (Fin 3 → Fin 2) → Prop) [DecidablePred Q]
    (hp : ∀ x : Fin 3 → Fin 2, (exampleLaw j).prob x = if Q x then c0 else 0) (hc : 0 ≤ c0)
    (hcard : c0 * (Finset.univ.filter Q).card = 1) : IsValidClassicalData (exampleLaw j) := by
  have hs : ∑ x : ClassicalBasis (exampleLaw j).dims, (exampleLaw j).prob x =
      ∑ x : Fin 3 → Fin 2, (if Q x then c0 else 0) := Finset.sum_congr rfl (fun x _ => hp x)
  refine ⟨fun i => by simp [exampleLaw], fun x => by rw [hp x]; split_ifs <;> simp [hc], hs.trans ?_⟩
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact hcard

theorem g64e_lb2 : Real.logb 2 (1/2 * (1:ℕ)) = -1 := by
  simp [Real.logb_inv]
theorem g64e_lb1 : Real.logb 2 (1/2 * (2:ℕ)) = -0 := by norm_num
theorem g64e_lb4 : Real.logb 2 (1/4 * (1:ℕ)) = -2 := by
  rw [show (1/4 * ((1:ℕ):ℝ)) = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.logb_pow, Real.logb_inv]; simp
theorem g64e_lb42 : Real.logb 2 (1/4 * (2:ℕ)) = -1 := by
  rw [show (1/4 * ((2:ℕ):ℝ)) = (2:ℝ)⁻¹ by norm_num, Real.logb_inv]; simp

theorem g64e_L0 : IsValidClassicalData (exampleLaw 0) ∧ ∀ i : Fin 5, fiveValues (exampleLaw 0) i = fiveTable 0 i := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 0).prob x = if (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) x then 1/2 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := g64e_lawsum 0 (1/2) (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp (by norm_num) (by rw [show (Finset.univ.filter (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0)).card = 2 by decide]; norm_num)
  have e0 := g64e_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {0} g64e_lb2 (by decide)
  have e1 := g64e_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {1} g64e_lb2 (by decide)
  have e2 := g64e_val3 0 (1/2) 2 0 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {2} g64e_lb1 (by decide)
  have e01 := g64e_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {0,1} g64e_lb2 (by decide)
  have e02 := g64e_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {0,2} g64e_lb2 (by decide)
  have e12 := g64e_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 {1,2} g64e_lb2 (by decide)
  have eU := g64e_val3 0 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 2 = 0) hp hv.2 Finset.univ g64e_lb2 (by decide)
  refine ⟨hv, fun i => ?_⟩
  rw [g64e_five _ hv  1 1 0 1 1 1 1 e0 e1 e2 e01 e02 e12 eU]
  fin_cases i <;> simp [fiveTable] <;> norm_num

theorem g64e_L1 : IsValidClassicalData (exampleLaw 1) ∧ ∀ i : Fin 5, fiveValues (exampleLaw 1) i = fiveTable 1 i := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 1).prob x = if (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) x then 1/2 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := g64e_lawsum 1 (1/2) (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp (by norm_num) (by rw [show (Finset.univ.filter (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0)).card = 2 by decide]; norm_num)
  have e0 := g64e_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {0} g64e_lb2 (by decide)
  have e1 := g64e_val3 1 (1/2) 2 0 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {1} g64e_lb1 (by decide)
  have e2 := g64e_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {2} g64e_lb2 (by decide)
  have e01 := g64e_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {0,1} g64e_lb2 (by decide)
  have e02 := g64e_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {0,2} g64e_lb2 (by decide)
  have e12 := g64e_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 {1,2} g64e_lb2 (by decide)
  have eU := g64e_val3 1 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 2 ∧ x 1 = 0) hp hv.2 Finset.univ g64e_lb2 (by decide)
  refine ⟨hv, fun i => ?_⟩
  rw [g64e_five _ hv  1 0 1 1 1 1 1 e0 e1 e2 e01 e02 e12 eU]
  fin_cases i <;> simp [fiveTable] <;> norm_num

theorem g64e_L2 : IsValidClassicalData (exampleLaw 2) ∧ ∀ i : Fin 5, fiveValues (exampleLaw 2) i = fiveTable 2 i := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 2).prob x = if (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) x then 1/2 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := g64e_lawsum 2 (1/2) (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp (by norm_num) (by rw [show (Finset.univ.filter (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0)).card = 2 by decide]; norm_num)
  have e0 := g64e_val3 2 (1/2) 2 0 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {0} g64e_lb1 (by decide)
  have e1 := g64e_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {1} g64e_lb2 (by decide)
  have e2 := g64e_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {2} g64e_lb2 (by decide)
  have e01 := g64e_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {0,1} g64e_lb2 (by decide)
  have e02 := g64e_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {0,2} g64e_lb2 (by decide)
  have e12 := g64e_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 {1,2} g64e_lb2 (by decide)
  have eU := g64e_val3 2 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 1 = x 2 ∧ x 0 = 0) hp hv.2 Finset.univ g64e_lb2 (by decide)
  refine ⟨hv, fun i => ?_⟩
  rw [g64e_five _ hv  0 1 1 1 1 1 1 e0 e1 e2 e01 e02 e12 eU]
  fin_cases i <;> simp [fiveTable] <;> norm_num

theorem g64e_L3 : IsValidClassicalData (exampleLaw 3) ∧ ∀ i : Fin 5, fiveValues (exampleLaw 3) i = fiveTable 3 i := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 3).prob x = if (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) x then 1/2 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := g64e_lawsum 3 (1/2) (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp (by norm_num) (by rw [show (Finset.univ.filter (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2)).card = 2 by decide]; norm_num)
  have e0 := g64e_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {0} g64e_lb2 (by decide)
  have e1 := g64e_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {1} g64e_lb2 (by decide)
  have e2 := g64e_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {2} g64e_lb2 (by decide)
  have e01 := g64e_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {0,1} g64e_lb2 (by decide)
  have e02 := g64e_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {0,2} g64e_lb2 (by decide)
  have e12 := g64e_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 {1,2} g64e_lb2 (by decide)
  have eU := g64e_val3 3 (1/2) 1 1 (fun x : Fin 3 → Fin 2 => x 0 = x 1 ∧ x 1 = x 2) hp hv.2 Finset.univ g64e_lb2 (by decide)
  refine ⟨hv, fun i => ?_⟩
  rw [g64e_five _ hv  1 1 1 1 1 1 1 e0 e1 e2 e01 e02 e12 eU]
  fin_cases i <;> simp [fiveTable] <;> norm_num

theorem g64e_L4 : IsValidClassicalData (exampleLaw 4) ∧ ∀ i : Fin 5, fiveValues (exampleLaw 4) i = fiveTable 4 i := by
  have hp : ∀ x : Fin 3 → Fin 2, (exampleLaw 4).prob x = if (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) x then 1/4 else 0 := by
    intro x; unfold exampleLaw; dsimp only; split_ifs <;> simp_all
  have hv := g64e_lawsum 4 (1/4) (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp (by norm_num) (by rw [show (Finset.univ.filter (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0)).card = 4 by decide]; norm_num)
  have e0 := g64e_val3 4 (1/4) 2 1 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {0} g64e_lb42 (by decide)
  have e1 := g64e_val3 4 (1/4) 2 1 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {1} g64e_lb42 (by decide)
  have e2 := g64e_val3 4 (1/4) 2 1 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {2} g64e_lb42 (by decide)
  have e01 := g64e_val3 4 (1/4) 1 2 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {0,1} g64e_lb4 (by decide)
  have e02 := g64e_val3 4 (1/4) 1 2 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {0,2} g64e_lb4 (by decide)
  have e12 := g64e_val3 4 (1/4) 1 2 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 {1,2} g64e_lb4 (by decide)
  have eU := g64e_val3 4 (1/4) 1 2 (fun x : Fin 3 → Fin 2 => ((x 0).val + (x 1).val + (x 2).val) % 2 = 0) hp hv.2 Finset.univ g64e_lb4 (by decide)
  refine ⟨hv, fun i => ?_⟩
  rw [g64e_five _ hv  1 1 1 2 2 2 2 e0 e1 e2 e01 e02 e12 eU]
  fin_cases i <;> simp [fiveTable] <;> norm_num


theorem g64e_two (q : CData 2) (hq : IsValidClassicalData q) :
    cValue .dual q = lawCMI q {0} {1} ∅ ∧ cValue .total q = lawCMI q {0} {1} ∅ := by
  have r0 : (Finset.univ.erase 0 : Finset (Fin 2)) = {1} := by decide
  have r1 : (Finset.univ.erase 1 : Finset (Fin 2)) = {0} := by decide
  have u : ({0} ∪ {1} ∪ ∅ : Finset (Fin 2)) = Finset.univ := by decide
  unfold lawCMI
  rw [g64e_dual, g64e_total, Fin.sum_univ_two, Fin.sum_univ_two, r0, r1, u]
  simp only [Finset.union_empty, g64e_cH_empty q hq]
  refine ⟨?_, ?_⟩ <;> norm_num <;> ring_nf

theorem g64e_id3 (p : CData 3) (hp : IsValidClassicalData p) :
    cValue .dual p = cH p {0,1} + cH p {1,2} + cH p {0,2} - 2*cH p Finset.univ ∧
    cValue .dual p = lawCMI p {0} {1,2} ∅ + lawCMI p {1} {2} {0} ∧
    cValue .total p = cH p {0} + cH p {1} + cH p {2} - cH p Finset.univ ∧
    cValue .total p = lawCMI p {0} {1} ∅ + lawCMI p {0,1} {2} ∅ := by
  have r0 : (Finset.univ.erase 0 : Finset (Fin 3)) = {1, 2} := by decide
  have r1 : (Finset.univ.erase 1 : Finset (Fin 3)) = {0, 2} := by decide
  have r2 : (Finset.univ.erase 2 : Finset (Fin 3)) = {0, 1} := by decide
  have s1 : ({0} ∪ {1, 2} ∪ ∅ : Finset (Fin 3)) = Finset.univ := by decide
  have s2 : ({1} ∪ {0} : Finset (Fin 3)) = {0, 1} := by decide
  have s3 : ({2} ∪ {0} : Finset (Fin 3)) = {0, 2} := by decide
  have s4 : ({1} ∪ {2} ∪ {0} : Finset (Fin 3)) = Finset.univ := by decide
  have s5 : ({0} ∪ {1} ∪ ∅ : Finset (Fin 3)) = {0, 1} := by decide
  have s6 : ({0, 1} ∪ {2} ∪ ∅ : Finset (Fin 3)) = Finset.univ := by decide
  unfold lawCMI
  rw [g64e_dual, g64e_total, Fin.sum_univ_three, Fin.sum_univ_three, r0, r1, r2, s1, s2, s3, s4, s5, s6]
  simp only [Finset.union_empty, g64e_cH_empty p hp]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> ring_nf

open QAlgorithms.Papers.Independent.Renew46.P37
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

section
open Classical

def g64e_ag {n : ℕ} {D : Fin n → ℕ} (s : Finset (Fin n)) (x y : ClassicalBasis D) : Prop :=
  ∀ i ∈ s, x i = y i

def g64e_M {n : ℕ} (p : CData n) (s : Finset (Fin n)) (y : ClassicalBasis p.dims) : ℝ :=
  ∑ x, if g64e_ag s x y then p.prob x else 0

theorem g64e_ag_symm {n : ℕ} {D : Fin n → ℕ} {s : Finset (Fin n)} {x y : ClassicalBasis D}
    (h : g64e_ag s x y) : g64e_ag s y x := fun i hi => (h i hi).symm

theorem g64e_ag_trans {n : ℕ} {D : Fin n → ℕ} {s : Finset (Fin n)} {x y z : ClassicalBasis D}
    (h : g64e_ag s x y) (h' : g64e_ag s y z) : g64e_ag s x z := fun i hi => (h i hi).trans (h' i hi)

theorem g64e_ag_mono {n : ℕ} {D : Fin n → ℕ} {s t : Finset (Fin n)} {x y : ClassicalBasis D}
    (hst : s ⊆ t) (h : g64e_ag t x y) : g64e_ag s x y := fun i hi => h i (hst hi)

theorem g64e_M_nonneg {n : ℕ} (p : CData n) (hp : IsValidClassicalData p) (s : Finset (Fin n)) (y) :
    0 ≤ g64e_M p s y :=
  Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hp.2.1 x]

theorem g64e_M_ge {n : ℕ} (p : CData n) (hp : IsValidClassicalData p) (s : Finset (Fin n)) (y) :
    p.prob y ≤ g64e_M p s y := by
  unfold g64e_M
  have := Finset.single_le_sum (f := fun x => if g64e_ag s x y then p.prob x else 0)
    (fun x _ => by split_ifs <;> simp [hp.2.1 x]) (Finset.mem_univ y)
  simpa [g64e_ag] using this

theorem g64e_M_congr {n : ℕ} (p : CData n) (s : Finset (Fin n)) {y y'} (h : g64e_ag s y y') :
    g64e_M p s y = g64e_M p s y' := by
  unfold g64e_M
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h1 : g64e_ag s x y
  · rw [if_pos h1, if_pos (g64e_ag_trans h1 h)]
  · rw [if_neg h1, if_neg (fun h2 => h1 (g64e_ag_trans h2 (g64e_ag_symm h)))]

theorem g64e_entropy {n : ℕ} (p : CData n) (s : Finset (Fin n)) :
    cH p s = -∑ y, p.prob y * Real.logb 2 (g64e_M p s y) := by
  unfold cH shannon
  congr 1
  set m := lawMarginal p s with hm_def
  have hm : ∀ y : ClassicalBasis p.dims, m (fun i => y i.val) = g64e_M p s y := by
    intro y
    simp only [hm_def, lawMarginal, g64e_M]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : g64e_ag s x y
    · rw [if_pos (fun (i : {i // i ∈ s}) => h i.1 i.2), if_pos h]
    · rw [if_neg (show ¬ (∀ i : {i // i ∈ s}, x i.val = y i.val) from
        fun h' => h fun i hi => h' ⟨i, hi⟩), if_neg h]
  have key : ∀ a (c : ℝ), m a * c =
      ∑ x : ClassicalBasis p.dims, if (fun (i : {i // i ∈ s}) => x i.val) = a then p.prob x * c else 0 := by
    intro a c
    simp only [hm_def, lawMarginal, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : (fun i : {i // i ∈ s} => x i.val) = a
    · rw [if_pos h, if_pos (fun (i : {i // i ∈ s}) => congrFun h i)]
    · rw [if_neg h, if_neg (show ¬ (∀ i : {i // i ∈ s}, x i.val = a i) from
        fun h' => h (funext h')), zero_mul]
  rw [Finset.sum_congr rfl fun a _ => key a (Real.logb 2 (m a)), Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), hm]

theorem g64e_F4 {n : ℕ} (p : CData n) (hp : IsValidClassicalData p) (U : Finset (Fin n)) (w) :
    ∑ y, (if g64e_ag U w y then p.prob y / g64e_M p U y else 0) ≤ 1 := by
  have : ∀ y, (if g64e_ag U w y then p.prob y / g64e_M p U y else 0) =
      (if g64e_ag U y w then p.prob y else 0) / g64e_M p U w := by
    intro y
    by_cases h : g64e_ag U w y
    · rw [if_pos h, if_pos (g64e_ag_symm h), g64e_M_congr p U (g64e_ag_symm h)]
    · rw [if_neg h, if_neg (fun h' => h (g64e_ag_symm h')), zero_div]
  rw [Finset.sum_congr rfl fun y _ => this y, ← Finset.sum_div]
  exact div_self_le_one _

theorem g64e_F5 {n : ℕ} (p : CData n) (hp : IsValidClassicalData p) (s t e : Finset (Fin n)) (x z) :
    ∑ y, (if g64e_ag (s ∪ e) x y ∧ g64e_ag (t ∪ e) z y then p.prob y / g64e_M p (s ∪ t ∪ e) y else 0)
      ≤ if g64e_ag e x z then 1 else 0 := by
  by_cases h : ∃ y0, g64e_ag (s ∪ e) x y0 ∧ g64e_ag (t ∪ e) z y0
  · obtain ⟨y0, h1, h2⟩ := h
    have hxz : g64e_ag e x z := fun i hi =>
      (h1 i (Finset.mem_union_right _ hi)).trans (h2 i (Finset.mem_union_right _ hi)).symm
    rw [if_pos hxz]
    have hc : ∀ y, (g64e_ag (s ∪ e) x y ∧ g64e_ag (t ∪ e) z y) ↔ g64e_ag (s ∪ t ∪ e) y0 y := by
      intro y
      constructor
      · rintro ⟨k1, k2⟩ i hi
        simp only [Finset.mem_union] at hi
        rcases hi with (hi | hi) | hi
        · exact (h1 i (by simp [hi])).symm.trans (k1 i (by simp [hi]))
        · exact (h2 i (by simp [hi])).symm.trans (k2 i (by simp [hi]))
        · exact (h1 i (by simp [hi])).symm.trans (k1 i (by simp [hi]))
      · intro k
        refine ⟨fun i hi => (h1 i hi).trans (k i ?_), fun i hi => (h2 i hi).trans (k i ?_)⟩
        · simp only [Finset.mem_union] at hi ⊢; tauto
        · simp only [Finset.mem_union] at hi ⊢; tauto
    calc _ = ∑ y, (if g64e_ag (s ∪ t ∪ e) y0 y then p.prob y / g64e_M p (s ∪ t ∪ e) y else 0) :=
          Finset.sum_congr rfl fun y _ => by
            by_cases hh : g64e_ag (s ∪ t ∪ e) y0 y
            · rw [if_pos ((hc y).2 hh), if_pos hh]
            · rw [if_neg (fun h' => hh ((hc y).1 h')), if_neg hh]
      _ ≤ 1 := g64e_F4 p hp _ y0
  · have : ∀ y, (if g64e_ag (s ∪ e) x y ∧ g64e_ag (t ∪ e) z y then
        p.prob y / g64e_M p (s ∪ t ∪ e) y else 0) = 0 := fun y => by
      rw [if_neg (fun h' => h ⟨y, h'⟩)]
    rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_const_zero]
    split_ifs <;> norm_num

theorem g64e_key {n : ℕ} (p : CData n) (hp : IsValidClassicalData p) (s t e : Finset (Fin n)) :
    ∑ y, p.prob y * (g64e_M p (s ∪ e) y * g64e_M p (t ∪ e) y /
      (g64e_M p e y * g64e_M p (s ∪ t ∪ e) y)) ≤ 1 := by
  set P := p.prob
  set MA := g64e_M p (s ∪ e)
  set MB := g64e_M p (t ∪ e)
  set Me := g64e_M p e
  set MU := g64e_M p (s ∪ t ∪ e)
  have step1 : ∀ y, P y * (MA y * MB y / (Me y * MU y)) =
      ∑ x, ∑ z, (if g64e_ag (s ∪ e) x y ∧ g64e_ag (t ∪ e) z y then
        P x * P z / Me x * (P y / MU y) else 0) := by
    intro y
    calc P y * (MA y * MB y / (Me y * MU y)) =
        (∑ x, if g64e_ag (s ∪ e) x y then P x else 0) * (∑ z, if g64e_ag (t ∪ e) z y then P z else 0)
          * (P y / MU y / Me y) := by
          simp only [MA, MB, g64e_M]; ring
      _ = ∑ x, ∑ z, (if g64e_ag (s ∪ e) x y then P x else 0) * (if g64e_ag (t ∪ e) z y then P z else 0)
          * (P y / MU y / Me y) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul]
      _ = _ := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
          by_cases h1 : g64e_ag (s ∪ e) x y
          · by_cases h2 : g64e_ag (t ∪ e) z y
            · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
              have : Me y = Me x := g64e_M_congr p e
                (g64e_ag_symm (g64e_ag_mono Finset.subset_union_right h1))
              rw [this]; ring
            · rw [if_neg h2, if_neg (show ¬(g64e_ag (s ∪ e) x y ∧ g64e_ag (t ∪ e) z y) from
                fun h => h2 h.2)]; ring
          · rw [if_neg h1, if_neg (show ¬(g64e_ag (s ∪ e) x y ∧ g64e_ag (t ∪ e) z y) from
                fun h => h1 h.1)]; ring
  rw [Finset.sum_congr rfl fun y _ => step1 y, Finset.sum_comm]
  have step2 : ∀ x, ∑ y, ∑ z, (if g64e_ag (s ∪ e) x y ∧ g64e_ag (t ∪ e) z y then
        P x * P z / Me x * (P y / MU y) else 0) ≤ P x := by
    intro x
    rw [Finset.sum_comm]
    have hb : ∀ z, ∑ y, (if g64e_ag (s ∪ e) x y ∧ g64e_ag (t ∪ e) z y then
        P x * P z / Me x * (P y / MU y) else 0) ≤ P x * P z / Me x * (if g64e_ag e x z then 1 else 0) := by
      intro z
      have hnn : 0 ≤ P x * P z / Me x :=
        div_nonneg (mul_nonneg (hp.2.1 x) (hp.2.1 z)) (g64e_M_nonneg p hp e x)
      calc _ = P x * P z / Me x * ∑ y, (if g64e_ag (s ∪ e) x y ∧ g64e_ag (t ∪ e) z y then
            P y / MU y else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            split_ifs <;> simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (g64e_F5 p hp s t e x z) hnn
    calc _ ≤ ∑ z, P x * P z / Me x * (if g64e_ag e x z then 1 else 0) := Finset.sum_le_sum fun z _ => hb z
      _ = P x / Me x * Me x := by
          simp only [Me, g64e_M, Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          by_cases h : g64e_ag e x z
          · rw [if_pos h, if_pos (g64e_ag_symm h)]; ring
          · rw [if_neg h, if_neg (fun h' => h (g64e_ag_symm h'))]; ring
      _ ≤ P x := by
          by_cases h0 : Me x = 0
          · rw [h0, mul_zero]; exact hp.2.1 x
          · rw [div_mul_cancel₀ _ h0]
  calc _ ≤ ∑ x, P x := Finset.sum_le_sum fun x _ => step2 x
    _ = 1 := hp.2.2

theorem g64e_cmi_nonneg {n : ℕ} (p : CData n) (hp : IsValidClassicalData p) (s t e : Finset (Fin n)) :
    0 ≤ lawCMI p s t e := by
  unfold lawCMI
  rw [g64e_entropy p (s ∪ e), g64e_entropy p (t ∪ e), g64e_entropy p e, g64e_entropy p (s ∪ t ∪ e)]
  set P := p.prob
  set MA := g64e_M p (s ∪ e)
  set MB := g64e_M p (t ∪ e)
  set Me := g64e_M p e
  set MU := g64e_M p (s ∪ t ∪ e)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : -(∑ y, P y * Real.logb 2 (MA y)) + -(∑ y, P y * Real.logb 2 (MB y)) -
      -(∑ y, P y * Real.logb 2 (Me y)) - -(∑ y, P y * Real.logb 2 (MU y)) =
      ∑ y, P y * (Real.logb 2 (MU y) + Real.logb 2 (Me y) - Real.logb 2 (MA y) - Real.logb 2 (MB y)) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring
  rw [h]
  have hterm : ∀ y, (P y - P y * (MA y * MB y / (Me y * MU y))) / Real.log 2 ≤
      P y * (Real.logb 2 (MU y) + Real.logb 2 (Me y) - Real.logb 2 (MA y) - Real.logb 2 (MB y)) := by
    intro y
    rcases (hp.2.1 y).lt_or_eq with hy | hy
    · have hA := lt_of_lt_of_le hy (g64e_M_ge p hp (s ∪ e) y)
      have hB := lt_of_lt_of_le hy (g64e_M_ge p hp (t ∪ e) y)
      have hE := lt_of_lt_of_le hy (g64e_M_ge p hp e y)
      have hU := lt_of_lt_of_le hy (g64e_M_ge p hp (s ∪ t ∪ e) y)
      set r := MA y * MB y / (Me y * MU y)
      have hr : 0 < r := by positivity
      have hlog : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr
      have hexp : Real.logb 2 (MU y) + Real.logb 2 (Me y) - Real.logb 2 (MA y) - Real.logb 2 (MB y) =
          -Real.log r / Real.log 2 := by
        simp only [Real.logb, r]
        rw [Real.log_div (by positivity) (by positivity), Real.log_mul hA.ne' hB.ne',
          Real.log_mul hE.ne' hU.ne']
        ring
      rw [hexp, div_le_iff₀ hl2]
      have : P y * (-Real.log r / Real.log 2) * Real.log 2 = P y * (-Real.log r) := by
        field_simp
      rw [this]
      nlinarith
    · have hP : P y = 0 := hy.symm
      rw [hP]; simp
  calc (0 : ℝ) ≤ (1 - ∑ y, P y * (MA y * MB y / (Me y * MU y))) / Real.log 2 := by
        apply div_nonneg _ hl2.le
        linarith [g64e_key p hp s t e]
    _ = ∑ y, (P y - P y * (MA y * MB y / (Me y * MU y))) / Real.log 2 := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, hp.2.2]
    _ ≤ _ := Finset.sum_le_sum fun y _ => hterm y
end


theorem g64e_cmi3 (p : CData 3) :
    lawCMI p {0} {1} {2} = cH p {0,2} + cH p {1,2} - cH p {2} - cH p Finset.univ ∧
    lawCMI p {1} {2} {0} = cH p {0,1} + cH p {0,2} - cH p {0} - cH p Finset.univ ∧
    lawCMI p {2} {0} {1} = cH p {1,2} + cH p {0,1} - cH p {1} - cH p Finset.univ ∧
    lawCMI p {0} {1} ∅ = cH p {0} + cH p {1} - cH p ∅ - cH p {0,1} ∧
    lawCMI p {1} {2} ∅ = cH p {1} + cH p {2} - cH p ∅ - cH p {1,2} ∧
    lawCMI p {2} {0} ∅ = cH p {2} + cH p {0} - cH p ∅ - cH p {0,2} := by
  have a1 : ({0} ∪ {1} : Finset (Fin 3)) = {0, 1} := by decide
  have a2 : ({1} ∪ {2} : Finset (Fin 3)) = {1, 2} := by decide
  have a3 : ({2} ∪ {0} : Finset (Fin 3)) = {0, 2} := by decide
  have a4 : ({1} ∪ {0} : Finset (Fin 3)) = {0, 1} := by decide
  have a5 : ({2} ∪ {1} : Finset (Fin 3)) = {1, 2} := by decide
  have a6 : ({0} ∪ {2} : Finset (Fin 3)) = {0, 2} := by decide
  have b1 : ({0, 1} ∪ {2} : Finset (Fin 3)) = Finset.univ := by decide
  have b2 : ({1, 2} ∪ {0} : Finset (Fin 3)) = Finset.univ := by decide
  have b3 : ({0, 2} ∪ {1} : Finset (Fin 3)) = Finset.univ := by decide
  unfold lawCMI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Finset.union_empty, a1, a2, a3, a4, a5, a6, b1, b2, b3]

theorem g64e_cone (p : CData 3) (hp : IsValidClassicalData p) :
    secrecyCoordinates p 3 = lawCMI p {1} {2} ∅ - lawCMI p {1} {2} {0} ∧
    secrecyCoordinates p 3 = lawCMI p {2} {0} ∅ - lawCMI p {2} {0} {1} ∧
    cValue .dual p = secrecyCoordinates p 0 + secrecyCoordinates p 1 + secrecyCoordinates p 2 +
      secrecyCoordinates p 3 ∧
    cValue .total p = secrecyCoordinates p 0 + secrecyCoordinates p 1 + secrecyCoordinates p 2 +
      2 * secrecyCoordinates p 3 ∧
    0 ≤ secrecyCoordinates p 0 ∧ 0 ≤ secrecyCoordinates p 1 ∧ 0 ≤ secrecyCoordinates p 2 ∧
    0 ≤ secrecyCoordinates p 0 + secrecyCoordinates p 3 ∧
    0 ≤ secrecyCoordinates p 1 + secrecyCoordinates p 3 ∧
    0 ≤ secrecyCoordinates p 2 + secrecyCoordinates p 3 ∧
    (∀ j, 0 ≤ formalYields p j) ∧
    (∀ i : Fin 5, fiveValues p i =
      formalYields p 0 * fiveTable 0 i + formalYields p 1 * fiveTable 2 i +
      formalYields p 2 * fiveTable 1 i +
      formalYields p 3 * fiveTable 4 i + formalYields p 4 * fiveTable 3 i) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := g64e_cmi3 p
  obtain ⟨d1, -, t1, -⟩ := g64e_id3 p hp
  have h0 := g64e_cH_empty p hp
  have n1 := g64e_cmi_nonneg p hp {0} {1} {2}
  have n2 := g64e_cmi_nonneg p hp {1} {2} {0}
  have n3 := g64e_cmi_nonneg p hp {2} {0} {1}
  have n4 := g64e_cmi_nonneg p hp {0} {1} ∅
  have n5 := g64e_cmi_nonneg p hp {1} {2} ∅
  have n6 := g64e_cmi_nonneg p hp {2} {0} ∅
  have v0 : secrecyCoordinates p 0 = lawCMI p {0} {1} {2} := rfl
  have v1 : secrecyCoordinates p 1 = lawCMI p {1} {2} {0} := rfl
  have v2 : secrecyCoordinates p 2 = lawCMI p {2} {0} {1} := rfl
  have v3 : secrecyCoordinates p 3 = lawCMI p {0} {1} ∅ - lawCMI p {0} {1} {2} := rfl
  have F := g64e_five p hp _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, ?_, ?_⟩
  · intro j
    simp only [formalYields]
    split_ifs with h
    · fin_cases j <;> simp <;> linarith
    · fin_cases j <;> simp <;> linarith
  · intro i
    rw [F]
    simp only [formalYields]
    split_ifs with h
    · fin_cases i <;> simp [fiveTable] <;> linarith
    · fin_cases i <;> simp [fiveTable] <;> linarith



open QAlgorithms.Papers.Independent.Renew46.P37

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

/-- §IV.D, PDF pp.8--9, (47)--(50): symmetry of u, the two identities,
all six positivity constraints, and nonnegative real yields with matching
monotone vectors. This asserts no physically reversible distillation protocol. -/
theorem solution (p : CData 3) (hp : IsValidClassicalData p) :
    let v := secrecyCoordinates p
    let y := formalYields p
    v 3 = lawCMI p {1} {2} ∅ - lawCMI p {1} {2} {0} ∧
    v 3 = lawCMI p {2} {0} ∅ - lawCMI p {2} {0} {1} ∧
    cValue .dual p = v 0 + v 1 + v 2 + v 3 ∧
    cValue .total p = v 0 + v 1 + v 2 + 2*v 3 ∧
    0 ≤ v 0 ∧ 0 ≤ v 1 ∧ 0 ≤ v 2 ∧
    0 ≤ v 0 + v 3 ∧ 0 ≤ v 1 + v 3 ∧ 0 ≤ v 2 + v 3 ∧
    (∀ j, 0 ≤ y j) ∧
    (∀ i : Fin 5, fiveValues p i =
      y 0 * fiveTable 0 i + y 1 * fiveTable 2 i + y 2 * fiveTable 1 i +
      y 3 * fiveTable 4 i + y 4 * fiveTable 3 i) := by
  exact g64e_cone p hp


end
