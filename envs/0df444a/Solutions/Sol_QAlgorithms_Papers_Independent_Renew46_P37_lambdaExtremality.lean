-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P37.lambdaExtremality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:56:25.504216+00:00
-- url     : https://prove2.me/submissions/ee4887ce-80b5-49c9-8aa3-d2263c583210

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_twoCopyConversions
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

theorem g64e_two (q : CData 2) (hq : IsValidClassicalData q) :
    cValue .dual q = lawCMI q {0} {1} ∅ ∧ cValue .total q = lawCMI q {0} {1} ∅ := by
  have r0 : (Finset.univ.erase 0 : Finset (Fin 2)) = {1} := by decide
  have r1 : (Finset.univ.erase 1 : Finset (Fin 2)) = {0} := by decide
  have u : ({0} ∪ {1} ∪ ∅ : Finset (Fin 2)) = Finset.univ := by decide
  unfold lawCMI
  rw [g64e_dual, g64e_total, Fin.sum_univ_two, Fin.sum_univ_two, r0, r1, u]
  simp only [Finset.union_empty, g64e_cH_empty q hq]
  refine ⟨?_, ?_⟩ <;> norm_num <;> ring_nf

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

section cmgen
open Classical

variable {Ω : Type*} [Fintype Ω]

def cmM {V : Type*} (P : Ω → ℝ) (f : Ω → V) (ω : Ω) : ℝ :=
  ∑ ω', if f ω' = f ω then P ω' else 0

def cmH {V : Type*} (P : Ω → ℝ) (f : Ω → V) : ℝ :=
  -∑ ω, P ω * Real.logb 2 (cmM P f ω)

theorem cm_M_congr {V : Type*} (P : Ω → ℝ) (f : Ω → V) {x y : Ω} (h : f x = f y) :
    cmM P f x = cmM P f y := by
  unfold cmM; rw [h]

theorem cm_M_nonneg {V : Type*} (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (f : Ω → V) (ω : Ω) :
    0 ≤ cmM P f ω :=
  Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hP x]

theorem cm_M_ge {V : Type*} (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (f : Ω → V) (ω : Ω) :
    P ω ≤ cmM P f ω := by
  unfold cmM
  have := Finset.single_le_sum (f := fun x => if f x = f ω then P x else 0)
    (fun x _ => by split_ifs <;> simp [hP x]) (Finset.mem_univ ω)
  simpa using this

theorem cm_H_congr {V W : Type*} (P : Ω → ℝ) (f : Ω → V) (g : Ω → W)
    (h : ∀ x y, f x = f y ↔ g x = g y) : cmH P f = cmH P g := by
  unfold cmH cmM
  simp only [h]

theorem cm_H_const {V : Type*} (P : Ω → ℝ) (hP1 : ∑ ω, P ω = 1) (v : V) :
    cmH P (fun _ => v) = 0 := by
  unfold cmH cmM; simp [hP1]

theorem cm_F4 {V : Type*} (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (f : Ω → V) (w : Ω) :
    ∑ y, (if f w = f y then P y / cmM P f y else 0) ≤ 1 := by
  have : ∀ y, (if f w = f y then P y / cmM P f y else 0) =
      (if f y = f w then P y else 0) / cmM P f w := by
    intro y
    by_cases h : f w = f y
    · rw [if_pos h, if_pos h.symm, cm_M_congr P f h]
    · rw [if_neg h, if_neg (fun h' => h h'.symm), zero_div]
  rw [Finset.sum_congr rfl fun y _ => this y, ← Finset.sum_div]
  exact div_self_le_one _

variable {A B E U : Type*}

theorem cm_key (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1)
    (fA : Ω → A) (fB : Ω → B) (fE : Ω → E) (fU : Ω → U)
    (hA : ∀ x y, fA x = fA y → fE x = fE y) (hB : ∀ x y, fB x = fB y → fE x = fE y)
    (hU : ∀ x y, fU x = fU y ↔ (fA x = fA y ∧ fB x = fB y)) :
    ∑ y, P y * (cmM P fA y * cmM P fB y / (cmM P fE y * cmM P fU y)) ≤ 1 := by
  set MA := cmM P fA
  set MB := cmM P fB
  set Me := cmM P fE
  set MU := cmM P fU
  have step1 : ∀ y, P y * (MA y * MB y / (Me y * MU y)) =
      ∑ x, ∑ z, (if fA x = fA y ∧ fB z = fB y then
        P x * P z / Me x * (P y / MU y) else 0) := by
    intro y
    calc P y * (MA y * MB y / (Me y * MU y)) =
        (∑ x, if fA x = fA y then P x else 0) * (∑ z, if fB z = fB y then P z else 0)
          * (P y / MU y / Me y) := by
          simp only [MA, MB, cmM]; ring
      _ = ∑ x, ∑ z, (if fA x = fA y then P x else 0) * (if fB z = fB y then P z else 0)
          * (P y / MU y / Me y) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul]
      _ = _ := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
          by_cases h1 : fA x = fA y
          · by_cases h2 : fB z = fB y
            · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
              have : Me y = Me x := cm_M_congr P fE (hA x y h1).symm
              rw [this]; ring
            · rw [if_neg h2, if_neg (show ¬(fA x = fA y ∧ fB z = fB y) from
                fun h => h2 h.2)]; ring
          · rw [if_neg h1, if_neg (show ¬(fA x = fA y ∧ fB z = fB y) from
                fun h => h1 h.1)]; ring
  rw [Finset.sum_congr rfl fun y _ => step1 y, Finset.sum_comm]
  have F5 : ∀ x z, ∑ y, (if fA x = fA y ∧ fB z = fB y then P y / MU y else 0)
      ≤ if fE x = fE z then 1 else 0 := by
    intro x z
    by_cases h : ∃ y0, fA x = fA y0 ∧ fB z = fB y0
    · obtain ⟨y0, h1, h2⟩ := h
      have hxz : fE x = fE z := (hA _ _ h1).trans (hB _ _ h2).symm
      rw [if_pos hxz]
      have hc : ∀ y, (fA x = fA y ∧ fB z = fB y) ↔ fU y0 = fU y := by
        intro y; rw [hU, h1, h2]
      calc _ = ∑ y, (if fU y0 = fU y then P y / MU y else 0) :=
            Finset.sum_congr rfl fun y _ => by
              by_cases hh : fU y0 = fU y
              · rw [if_pos ((hc y).2 hh), if_pos hh]
              · rw [if_neg (fun h' => hh ((hc y).1 h')), if_neg hh]
        _ ≤ 1 := cm_F4 P hP fU y0
    · have : ∀ y, (if fA x = fA y ∧ fB z = fB y then P y / MU y else 0) = 0 := fun y => by
        rw [if_neg (fun h' => h ⟨y, h'⟩)]
      rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_const_zero]
      split_ifs <;> norm_num
  have step2 : ∀ x, ∑ y, ∑ z, (if fA x = fA y ∧ fB z = fB y then
        P x * P z / Me x * (P y / MU y) else 0) ≤ P x := by
    intro x
    rw [Finset.sum_comm]
    have hb : ∀ z, ∑ y, (if fA x = fA y ∧ fB z = fB y then
        P x * P z / Me x * (P y / MU y) else 0) ≤ P x * P z / Me x * (if fE x = fE z then 1 else 0) := by
      intro z
      have hnn : 0 ≤ P x * P z / Me x :=
        div_nonneg (mul_nonneg (hP x) (hP z)) (cm_M_nonneg P hP fE x)
      calc _ = P x * P z / Me x * ∑ y, (if fA x = fA y ∧ fB z = fB y then
            P y / MU y else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            split_ifs <;> simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (F5 x z) hnn
    calc _ ≤ ∑ z, P x * P z / Me x * (if fE x = fE z then 1 else 0) := Finset.sum_le_sum fun z _ => hb z
      _ = P x / Me x * Me x := by
          simp only [Me, cmM, Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          by_cases h : fE x = fE z
          · rw [if_pos h, if_pos h.symm]; ring
          · rw [if_neg h, if_neg (fun h' => h h'.symm)]; ring
      _ ≤ P x := by
          by_cases h0 : Me x = 0
          · rw [h0, mul_zero]; exact hP x
          · rw [div_mul_cancel₀ _ h0]
  calc _ ≤ ∑ x, P x := Finset.sum_le_sum fun x _ => step2 x
    _ = 1 := hP1

theorem cm_cmi (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1)
    (fA : Ω → A) (fB : Ω → B) (fE : Ω → E) (fU : Ω → U)
    (hA : ∀ x y, fA x = fA y → fE x = fE y) (hB : ∀ x y, fB x = fB y → fE x = fE y)
    (hU : ∀ x y, fU x = fU y ↔ (fA x = fA y ∧ fB x = fB y)) :
    0 ≤ cmH P fA + cmH P fB - cmH P fE - cmH P fU := by
  unfold cmH
  set MA := cmM P fA
  set MB := cmM P fB
  set Me := cmM P fE
  set MU := cmM P fU
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : -(∑ y, P y * Real.logb 2 (MA y)) + -(∑ y, P y * Real.logb 2 (MB y)) -
      -(∑ y, P y * Real.logb 2 (Me y)) - -(∑ y, P y * Real.logb 2 (MU y)) =
      ∑ y, P y * (Real.logb 2 (MU y) + Real.logb 2 (Me y) - Real.logb 2 (MA y) - Real.logb 2 (MB y)) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring
  rw [h]
  have hterm : ∀ y, (P y - P y * (MA y * MB y / (Me y * MU y))) / Real.log 2 ≤
      P y * (Real.logb 2 (MU y) + Real.logb 2 (Me y) - Real.logb 2 (MA y) - Real.logb 2 (MB y)) := by
    intro y
    rcases (hP y).lt_or_eq with hy | hy
    · have hA' := lt_of_lt_of_le hy (cm_M_ge P hP fA y)
      have hB' := lt_of_lt_of_le hy (cm_M_ge P hP fB y)
      have hE' := lt_of_lt_of_le hy (cm_M_ge P hP fE y)
      have hU' := lt_of_lt_of_le hy (cm_M_ge P hP fU y)
      set r := MA y * MB y / (Me y * MU y)
      have hr : 0 < r := by positivity
      have hlog : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr
      have hexp : Real.logb 2 (MU y) + Real.logb 2 (Me y) - Real.logb 2 (MA y) - Real.logb 2 (MB y) =
          -Real.log r / Real.log 2 := by
        simp only [Real.logb, r]
        rw [Real.log_div (by positivity) (by positivity), Real.log_mul hA'.ne' hB'.ne',
          Real.log_mul hE'.ne' hU'.ne']
        ring
      rw [hexp, div_le_iff₀ hl2]
      have : P y * (-Real.log r / Real.log 2) * Real.log 2 = P y * (-Real.log r) := by
        field_simp
      rw [this]
      nlinarith
    · have hP0 : P y = 0 := hy.symm
      rw [hP0]; simp
  calc (0 : ℝ) ≤ (1 - ∑ y, P y * (MA y * MB y / (Me y * MU y))) / Real.log 2 := by
        apply div_nonneg _ hl2.le
        linarith [cm_key P hP hP1 fA fB fE fU hA hB hU]
    _ = ∑ y, (P y - P y * (MA y * MB y / (Me y * MU y))) / Real.log 2 := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, hP1]
    _ ≤ _ := Finset.sum_le_sum fun y _ => hterm y

end cmgen

section cmgen2
open Classical

theorem cm_fst {α β V : Type*} [Fintype α] [Fintype β] (P : α → ℝ) (K : α → β → ℝ)
    (hK1 : ∀ x, ∑ c, K x c = 1) (f : α → V) :
    cmH (fun z : α × β => P z.1 * K z.1 z.2) (fun z => f z.1) = cmH P f := by
  have hM : ∀ z : α × β, cmM (fun z : α × β => P z.1 * K z.1 z.2) (fun z => f z.1) z =
      cmM P f z.1 := by
    intro z
    unfold cmM
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · show ∑ c, P x * K x c = P x
      rw [← Finset.mul_sum, hK1, mul_one]
    · simp
  unfold cmH
  simp only [hM]
  rw [Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_mul, hK1, one_mul]

theorem cm_withK {α β V : Type*} [Fintype α] [Fintype β] (P : α → ℝ) (K : α → β → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hK0 : ∀ x c, 0 ≤ K x c)
    (hK1 : ∀ x, ∑ c, K x c = 1) (f : α → V) (hK : ∀ x x', f x' = f x → K x' = K x) :
    cmH (fun z : α × β => P z.1 * K z.1 z.2) (fun z => (f z.1, z.2)) =
      cmH P f - ∑ x, ∑ c, P x * K x c * Real.logb 2 (K x c) := by
  have hM : ∀ z : α × β, cmM (fun z : α × β => P z.1 * K z.1 z.2) (fun z => (f z.1, z.2)) z =
      K z.1 z.2 * cmM P f z.1 := by
    intro z
    unfold cmM
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Prod.mk.injEq]
    by_cases h : f x = f z.1
    · simp only [h, true_and]
      rw [Finset.sum_ite_eq' Finset.univ z.2 (fun c => P x * K x c), if_pos (Finset.mem_univ _),
        hK z.1 x h, if_pos trivial]; ring
    · simp [h]
  unfold cmH
  simp only [hM]
  rw [Fintype.sum_prod_type]
  have hterm : ∀ x c, P x * K x c * Real.logb 2 (K x c * cmM P f x) =
      P x * K x c * Real.logb 2 (K x c) + K x c * (P x * Real.logb 2 (cmM P f x)) := by
    intro x c
    rcases (mul_nonneg (hP x) (hK0 x c)).lt_or_eq with h | h
    · have hp : 0 < P x := pos_of_mul_pos_left h (hK0 x c) |> fun h' => by
        rcases (hP x).lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1, zero_mul] at h; exact absurd h (lt_irrefl 0)
      have hk : 0 < K x c := by
        rcases (hK0 x c).lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1, mul_zero] at h; exact absurd h (lt_irrefl 0)
      have hm := lt_of_lt_of_le hp (cm_M_ge P hP f x)
      rw [Real.logb_mul hk.ne' hm.ne']; ring
    · rw [← h]
      have : P x * K x c * Real.logb 2 (cmM P f x) = 0 := by rw [← h, zero_mul]
      linarith [this]
  simp only [hterm, Finset.sum_add_distrib]
  have : ∀ x, ∑ c, K x c * (P x * Real.logb 2 (cmM P f x)) = P x * Real.logb 2 (cmM P f x) := by
    intro x; rw [← Finset.sum_mul, hK1, one_mul]
  simp only [this]; ring

theorem cm_dist_key {Ω V : Type*} [Fintype Ω] (P : Ω → ℝ) (f : Ω → V) (T : Finset V)
    (hT : ∀ ω, f ω ∈ T) : cmH P f =
      -∑ v ∈ T, (∑ ω, (if f ω = v then P ω else 0)) *
        Real.logb 2 (∑ ω, (if f ω = v then P ω else 0)) := by
  unfold cmH cmM
  congr 1
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := T) (g := f) (fun i _ => hT i)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs with h
  · subst h; rfl
  · simp

theorem cm_dist {Ω Ω' V : Type*} [Fintype Ω] [Fintype Ω'] (P : Ω → ℝ) (P' : Ω' → ℝ)
    (f : Ω → V) (g : Ω' → V)
    (hd : ∀ v, ∑ ω, (if f ω = v then P ω else 0) = ∑ ω, (if g ω = v then P' ω else 0)) :
    cmH P f = cmH P' g := by
  classical
  let T := Finset.univ.image f ∪ Finset.univ.image g
  rw [cm_dist_key P f T (fun ω => by simp [T]), cm_dist_key P' g T (fun ω => by simp [T])]
  simp only [hd]

theorem cm_sigma {k : ℕ} {Y : Fin k → Type*} [∀ j, Fintype (Y j)] {V : Type*}
    (w : Fin k → ℝ) (R : ∀ j, Y j → ℝ) (g : ∀ j, Y j → V)
    (hw : ∀ j, 0 ≤ w j) (hR : ∀ j y, 0 ≤ R j y) (hR1 : ∀ j, ∑ y, R j y = 1) :
    cmH (fun z : (Σ j, Y j) => w z.1 * R z.1 z.2) (fun z => (z.1, g z.1 z.2)) =
      -∑ j, w j * Real.logb 2 (w j) + ∑ j, w j * cmH (R j) (g j) := by
  have hM : ∀ z : (Σ j, Y j), cmM (fun z : (Σ j, Y j) => w z.1 * R z.1 z.2)
      (fun z => (z.1, g z.1 z.2)) z = w z.1 * cmM (R z.1) (g z.1) z.2 := by
    rintro ⟨j, y⟩
    unfold cmM
    rw [Fintype.sum_sigma, Finset.sum_eq_single j]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y' _ => ?_
      simp only [Prod.mk.injEq, true_and]
      split_ifs <;> simp
    · intro j' _ hj'
      refine Finset.sum_eq_zero fun y' _ => ?_
      simp only [Prod.mk.injEq]
      rw [if_neg (fun h => hj' h.1)]
    · simp
  unfold cmH
  simp only [hM]
  rw [Fintype.sum_sigma]
  have hterm : ∀ j y, w j * R j y * Real.logb 2 (w j * cmM (R j) (g j) y) =
      R j y * (w j * Real.logb 2 (w j)) + w j * (R j y * Real.logb 2 (cmM (R j) (g j) y)) := by
    intro j y
    rcases (hw j).lt_or_eq with h1 | h1
    · rcases (hR j y).lt_or_eq with h2 | h2
      · have hm := lt_of_lt_of_le h2 (cm_M_ge (R j) (hR j) (g j) y)
        rw [Real.logb_mul h1.ne' hm.ne']; ring
      · rw [← h2]; ring
    · rw [← h1]; ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hR1, one_mul, ← Finset.mul_sum]
  simp only [neg_add, mul_neg, Finset.sum_neg_distrib]

theorem cm_prod {α β V W : Type*} [Fintype α] [Fintype β] (P1 : α → ℝ) (P2 : β → ℝ)
    (hP1 : ∀ x, 0 ≤ P1 x) (hP2 : ∀ x, 0 ≤ P2 x) (h1 : ∑ x, P1 x = 1) (h2 : ∑ x, P2 x = 1)
    (f1 : α → V) (f2 : β → W) :
    cmH (fun z : α × β => P1 z.1 * P2 z.2) (fun z => (f1 z.1, f2 z.2)) =
      cmH P1 f1 + cmH P2 f2 := by
  have hM : ∀ z : α × β, cmM (fun z : α × β => P1 z.1 * P2 z.2) (fun z => (f1 z.1, f2 z.2)) z =
      cmM P1 f1 z.1 * cmM P2 f2 z.2 := by
    intro z
    unfold cmM
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Prod.mk.injEq]
    by_cases ha : f1 a = f1 z.1 <;> by_cases hb : f2 b = f2 z.2 <;> simp [ha, hb]
  unfold cmH
  simp only [hM]
  rw [Fintype.sum_prod_type]
  have hterm : ∀ a b, P1 a * P2 b * Real.logb 2 (cmM P1 f1 a * cmM P2 f2 b) =
      P2 b * (P1 a * Real.logb 2 (cmM P1 f1 a)) + P1 a * (P2 b * Real.logb 2 (cmM P2 f2 b)) := by
    intro a b
    rcases (hP1 a).lt_or_eq with ha | ha
    · rcases (hP2 b).lt_or_eq with hb | hb
      · rw [Real.logb_mul (lt_of_lt_of_le ha (cm_M_ge P1 hP1 f1 a)).ne'
          (lt_of_lt_of_le hb (cm_M_ge P2 hP2 f2 b)).ne']; ring
      · rw [← hb]; ring
    · rw [← ha]; ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, h2, one_mul]
  simp only [h1, one_mul]; ring

def cmV {n : ℕ} {d : Fin n → ℕ} (S : Finset (Fin n)) (x : ClassicalBasis d) : Fin n → ℕ :=
  fun i => if i ∈ S then (x i).val else 0

theorem cmV_eq {n : ℕ} {d : Fin n → ℕ} (S : Finset (Fin n)) (x y : ClassicalBasis d) :
    cmV S x = cmV S y ↔ ∀ i ∈ S, x i = y i := by
  constructor
  · intro h i hi
    have := congrFun h i
    simp only [cmV, if_pos hi] at this
    exact Fin.ext this
  · intro h; funext i
    simp only [cmV]
    split_ifs with hi
    · rw [h i hi]
    · rfl

theorem cm_cH {n : ℕ} (p : CData n) (S : Finset (Fin n)) :
    cH p S = cmH p.prob (cmV S) := by
  rw [g64e_entropy]
  unfold cmH cmM g64e_M g64e_ag
  simp only [cmV_eq]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 2
  exact Finset.sum_congr rfl fun y _ => by congr

end cmgen2

section cmslot
open Classical

def cmFill {S : Type} [DecidableEq S] (d d' : S → ℕ) (s0 : S)
    (hd : ∀ i, i ≠ s0 → d' i = d i) (u : (i : S) → Fin (d i)) (c : Fin (d' s0)) :
    (i : S) → Fin (d' i) := fun i =>
  if h : i = s0 then ⟨c.val, by subst h; exact c.isLt⟩
  else ⟨(u i).val, by rw [hd i h]; exact (u i).isLt⟩

theorem cmFill_s0 {S : Type} [DecidableEq S] (d d' : S → ℕ) (s0 : S)
    (hd : ∀ i, i ≠ s0 → d' i = d i) (u : (i : S) → Fin (d i)) (c : Fin (d' s0)) :
    cmFill d d' s0 hd u c s0 = c := Fin.ext (by simp [cmFill])

theorem cmFill_ne {S : Type} [DecidableEq S] (d d' : S → ℕ) (s0 : S)
    (hd : ∀ i, i ≠ s0 → d' i = d i) (u : (i : S) → Fin (d i)) (c : Fin (d' s0)) (i : S)
    (hi : i ≠ s0) : (cmFill d d' s0 hd u c i).val = (u i).val := by simp [cmFill, hi]

theorem cm_sum_slot {S : Type} [Fintype S] [DecidableEq S] (d d' : S → ℕ) (s0 : S)
    (hd : ∀ i, i ≠ s0 → d' i = d i) (u : (i : S) → Fin (d i)) (φ : ((i : S) → Fin (d' i)) → ℝ)
    (inst : ∀ F : (i : S) → Fin (d' i), Decidable (∀ i, i ≠ s0 → (u i).val = (F i).val)) :
    ∑ F : (i : S) → Fin (d' i),
      φ F * (@ite ℝ (∀ i, i ≠ s0 → (u i).val = (F i).val) (inst F) 1 0) =
      ∑ c, φ (cmFill d d' s0 hd u c) := by
  symm
  refine Fintype.sum_of_injective (cmFill d d' s0 hd u) (fun c c' h => by
    rw [← cmFill_s0 d d' s0 hd u c, ← cmFill_s0 d d' s0 hd u c', h]) _ _ ?_ ?_
  · intro F hF
    rw [if_neg, mul_zero]
    intro hc
    apply hF
    refine ⟨F s0, funext fun i => ?_⟩
    by_cases hi : i = s0
    · subst hi; exact cmFill_s0 _ _ _ _ _ _
    · exact Fin.ext (by rw [cmFill_ne _ _ _ _ _ _ _ hi, hc i hi])
  · intro c
    rw [if_pos, mul_one]
    intro i hi
    rw [cmFill_ne _ _ _ _ _ _ _ hi]

end cmslot

section cmmono
open Classical
variable {n k : ℕ} (p : CData n) (w : Fin k → ℝ) (r : Fin k → CData n) (π : Fin n)
  (K : (j : Fin k) → Fin (p.dims π) → Fin ((r j).dims π) → ℝ)

abbrev cmΩ := ClassicalBasis p.dims × (Σ j : Fin k, Fin ((r j).dims π))

def cmKc (x : ClassicalBasis p.dims) (c : Σ j : Fin k, Fin ((r j).dims π)) : ℝ := K c.1 (x π) c.2

def cmVf (S : Finset (Fin n)) (z : cmΩ p r π) : Fin k × (Fin n → ℕ) :=
  (z.2.1, fun i => if i ∈ S then (if i = π then z.2.2.val else (z.1 i).val) else 0)

theorem cm_Kc1 (hK1 : ∀ a, (∑ j, ∑ b, K j a b) = 1) (x : ClassicalBasis p.dims) :
    ∑ c, cmKc p r π K x c = 1 := by
  simp only [cmKc]; rw [Fintype.sum_sigma]; exact hK1 _

theorem cm_a (hK1 : ∀ a, (∑ j, ∑ b, K j a b) = 1) (S : Finset (Fin n)) :
    cmH (fun z : cmΩ p r π => p.prob z.1 * cmKc p r π K z.1 z.2) (fun z => cmV S z.1) = cH p S := by
  rw [cm_fst _ _ (cm_Kc1 p r π K hK1), cm_cH]

theorem cm_c (hp : IsValidClassicalData p) (hK0 : ∀ j a b, 0 ≤ K j a b)
    (hK1 : ∀ a, (∑ j, ∑ b, K j a b) = 1) (S : Finset (Fin n)) (hS : π ∈ S) :
    cmH (fun z : cmΩ p r π => p.prob z.1 * cmKc p r π K z.1 z.2) (fun z => (cmV S z.1, z.2)) =
      cH p S - ∑ x, ∑ c, p.prob x * cmKc p r π K x c * Real.logb 2 (cmKc p r π K x c) := by
  rw [cm_withK p.prob (cmKc p r π K) hp.2.1 (fun x c => hK0 _ _ _) (cm_Kc1 p r π K hK1), cm_cH]
  intro x x' h
  have := ((cmV_eq S x' x).1 h) π hS
  funext c; simp only [cmKc, this]

theorem cm_b (hw : IsLaw w) (hr : ∀ j, IsValidClassicalData (r j))
    (hdim : ∀ j i, i ≠ π → (r j).dims i = p.dims i)
    (hEq : ∀ j (y : ClassicalBasis (r j).dims),
      w j * (r j).prob y = ∑ x : ClassicalBasis p.dims,
        if ∀ i, i ≠ π → (x i).val = (y i).val
        then p.prob x * K j (x π) (y π) else 0) (S : Finset (Fin n)) :
    cmH (fun z : cmΩ p r π => p.prob z.1 * cmKc p r π K z.1 z.2) (cmVf p r π S) =
      -∑ j, w j * Real.logb 2 (w j) + ∑ j, w j * cH (r j) S := by
  simp only [cm_cH]
  rw [← cm_sigma w (fun j => (r j).prob) (fun j => cmV S) hw.1 (fun j => (hr j).2.1)
    (fun j => (hr j).2.2)]
  apply cm_dist
  rintro ⟨j0, u⟩
  rw [Fintype.sum_prod_type, Fintype.sum_sigma, Finset.sum_eq_single j0]
  · simp only [Prod.mk.injEq, true_and]
    have hR : ∀ y : ClassicalBasis (r j0).dims, (if cmV S y = u then w j0 * (r j0).prob y else 0) =
        ∑ x : ClassicalBasis p.dims, (p.prob x * K j0 (x π) (y π) *
          (if cmV S y = u then 1 else 0)) *
          (if ∀ i, i ≠ π → (x i).val = (y i).val then 1 else 0) := by
      intro y
      split_ifs with h1
      · rw [hEq j0 y]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp
      · simp
    simp only [hR]
    rw [Finset.sum_comm (γ := ClassicalBasis (r j0).dims)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_sigma, Finset.sum_eq_single j0]
    · refine Eq.trans ?_ (cm_sum_slot p.dims (r j0).dims π (hdim j0) x
        (fun y => p.prob x * K j0 (x π) (y π) * (if cmV S y = u then 1 else 0)) _).symm
      refine Finset.sum_congr rfl fun b _ => ?_
      try dsimp only
      rw [cmFill_s0]
      have hv : cmV S (cmFill p.dims (r j0).dims π (hdim j0) x b) =
          (fun i => if i ∈ S then (if i = π then b.val else (x i).val) else 0) := by
        funext i
        simp only [cmV]
        split_ifs with h1 h2
        · subst h2; rw [cmFill_s0]
        · rw [cmFill_ne _ _ _ _ _ _ _ h2]
        · rfl
      rw [hv]
      simp only [cmVf, cmKc, Prod.mk.injEq, true_and]
      split_ifs <;> simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun b _ => ?_
      simp only [cmVf, Prod.mk.injEq]
      rw [if_neg (fun h => hj h.1)]
    · simp
  · intro j _ hj
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [Prod.mk.injEq]
    rw [if_neg (fun h => hj h.1)]
  · simp

end cmmono

section cmmono2
open Classical
variable {n k : ℕ} (p : CData n) (w : Fin k → ℝ) (r : Fin k → CData n) (π : Fin n)
  (K : (j : Fin k) → Fin (p.dims π) → Fin ((r j).dims π) → ℝ)

theorem cmVf_eq (S : Finset (Fin n)) (z z' : cmΩ p r π) :
    cmVf p r π S z = cmVf p r π S z' ↔ z.2.1 = z'.2.1 ∧
      ∀ i ∈ S, (i = π → z.2.2.val = z'.2.2.val) ∧ (i ≠ π → (z.1 i).val = (z'.1 i).val) := by
  simp only [cmVf, Prod.mk.injEq, funext_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h i hi
    have := h i
    simp only [hi, if_true] at this
    by_cases hπ : i = π
    · rw [if_pos hπ, if_pos hπ] at this; exact ⟨fun _ => this, fun h => absurd hπ h⟩
    · rw [if_neg hπ, if_neg hπ] at this; exact ⟨fun h => absurd h hπ, fun _ => this⟩
  · intro h i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      by_cases hπ : i = π
      · simp only [hπ, if_true]; exact (h i hi).1 hπ
      · simp only [hπ, if_false]; exact (h i hi).2 hπ
    · simp only [hi, if_false]

theorem cm_ineqA (hp : IsValidClassicalData p) (hw : IsLaw w) (hr : ∀ j, IsValidClassicalData (r j))
    (hK0 : ∀ j a b, 0 ≤ K j a b) (hK1 : ∀ a, (∑ j, ∑ b, K j a b) = 1)
    (hdim : ∀ j i, i ≠ π → (r j).dims i = p.dims i)
    (hEq : ∀ j (y : ClassicalBasis (r j).dims),
      w j * (r j).prob y = ∑ x : ClassicalBasis p.dims,
        if ∀ i, i ≠ π → (x i).val = (y i).val
        then p.prob x * K j (x π) (y π) else 0)
    (S : Finset (Fin n)) (hS : π ∉ S) :
    ∑ j, w j * cH (r j) S ≤ cH p S := by
  have hQ0 : ∀ z : cmΩ p r π, 0 ≤ p.prob z.1 * cmKc p r π K z.1 z.2 :=
    fun z => mul_nonneg (hp.2.1 _) (hK0 _ _ _)
  have hQ1 : ∑ z : cmΩ p r π, p.prob z.1 * cmKc p r π K z.1 z.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, cm_Kc1 p r π K hK1, mul_one]; exact hp.2.2
  have h := cm_cmi _ hQ0 hQ1 (cmVf p r π ∅) (fun z => cmV S z.1) (fun _ => ())
    (cmVf p r π S) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (by
      intro x y
      rw [cmVf_eq, cmVf_eq, cmV_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, fun i hi => absurd hi (Finset.notMem_empty _)⟩, fun i hi => Fin.ext ?_⟩
        exact (h2 i hi).2 (fun h => hS (h ▸ hi))
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, fun i hi => ⟨fun h => absurd (h ▸ hi) hS, fun _ => by rw [h2 i hi]⟩⟩)
  rw [cm_b p w r π K hw hr hdim hEq, cm_b p w r π K hw hr hdim hEq, cm_a p r π K hK1,
    cm_H_const _ hQ1] at h
  have h0 : ∑ j, w j * cH (r j) ∅ = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [g64e_cH_empty _ (hr j), mul_zero]
  linarith

theorem cm_ineqB (hp : IsValidClassicalData p) (hw : IsLaw w) (hr : ∀ j, IsValidClassicalData (r j))
    (hK0 : ∀ j a b, 0 ≤ K j a b) (hK1 : ∀ a, (∑ j, ∑ b, K j a b) = 1)
    (hdim : ∀ j i, i ≠ π → (r j).dims i = p.dims i)
    (hEq : ∀ j (y : ClassicalBasis (r j).dims),
      w j * (r j).prob y = ∑ x : ClassicalBasis p.dims,
        if ∀ i, i ≠ π → (x i).val = (y i).val
        then p.prob x * K j (x π) (y π) else 0)
    (T : Finset (Fin n)) (hT : π ∈ T) :
    ∑ j, w j * cH (r j) T - ∑ j, w j * cH (r j) Finset.univ ≤ cH p T - cH p Finset.univ := by
  have hQ0 : ∀ z : cmΩ p r π, 0 ≤ p.prob z.1 * cmKc p r π K z.1 z.2 :=
    fun z => mul_nonneg (hp.2.1 _) (hK0 _ _ _)
  have hQ1 : ∑ z : cmΩ p r π, p.prob z.1 * cmKc p r π K z.1 z.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, cm_Kc1 p r π K hK1, mul_one]; exact hp.2.2
  have h := cm_cmi _ hQ0 hQ1 (fun z : cmΩ p r π => (cmV T z.1, z.2)) (cmVf p r π Finset.univ)
    (cmVf p r π T) (fun z : cmΩ p r π => (cmV Finset.univ z.1, z.2))
    (by
      intro x y hxy
      rw [Prod.mk.injEq, cmV_eq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      rw [cmVf_eq, h2]
      exact ⟨rfl, fun i hi => ⟨fun _ => rfl, fun _ => by rw [h1 i hi]⟩⟩)
    (by
      intro x y hxy
      rw [cmVf_eq] at hxy ⊢
      exact ⟨hxy.1, fun i _ => hxy.2 i (Finset.mem_univ _)⟩)
    (by
      intro x y
      rw [Prod.mk.injEq, Prod.mk.injEq, cmV_eq, cmV_eq, cmVf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨fun i _ => h1 i (Finset.mem_univ _), h2⟩, ?_⟩
        rw [h2]
        exact ⟨rfl, fun i _ => ⟨fun _ => rfl, fun _ => by rw [h1 i (Finset.mem_univ _)]⟩⟩
      · rintro ⟨⟨h1, h2⟩, _, h3⟩
        refine ⟨fun i _ => ?_, h2⟩
        by_cases hi : i = π
        · subst hi; exact h1 _ hT
        · exact Fin.ext ((h3 i (Finset.mem_univ _)).2 hi))
  rw [cm_b p w r π K hw hr hdim hEq, cm_b p w r π K hw hr hdim hEq,
    cm_c p r π K hp hK0 hK1 _ hT, cm_c p r π K hp hK0 hK1 _ (Finset.mem_univ _)] at h
  linarith

end cmmono2

section cmmono3
open Classical

theorem cm_mono {n : ℕ} (kind : InformationKind) (p : CData n) (k : ℕ) (w : Fin k → ℝ)
    (r : Fin k → CData n) (h : CInstrument p w r) :
    (∑ j, w j * cValue kind (r j)) ≤ cValue kind p := by
  obtain ⟨hp, hw, hr, π, K, hdim, hK0, hK1, hEq⟩ := h
  have hA := cm_ineqA p w r π K hp hw hr hK0 hK1 hdim hEq
  have hB := cm_ineqB p w r π K hp hw hr hK0 hK1 hdim hEq
  set A : Finset (Fin n) → ℝ := fun S => ∑ j, w j * cH (r j) S with hAdef
  have hsplit : ∀ f : Fin n → ℝ, ∑ i, f i = f π + ∑ i ∈ Finset.univ.erase π, f i := fun f =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ π)).symm
  have hcard : ((n - 1 : ℕ) : ℝ) = ∑ i ∈ Finset.univ.erase π, (1 : ℝ) := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  cases kind with
  | dual =>
    simp only [g64e_dual]
    have e1 : ∑ j, w j * ((∑ i, cH (r j) (Finset.univ.erase i)) - (n - 1 : ℕ) * cH (r j) Finset.univ)
        = (∑ i, A (Finset.univ.erase i)) - (n - 1 : ℕ) * A Finset.univ := by
      simp only [hAdef, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]; congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e1, hsplit, hsplit, hcard, Finset.sum_mul, Finset.sum_mul]
    have h1 := hA (Finset.univ.erase π) (by simp)
    have h2 : ∀ i ∈ Finset.univ.erase π, A (Finset.univ.erase i) - 1 * A Finset.univ ≤
        cH p (Finset.univ.erase i) - 1 * cH p Finset.univ := by
      intro i hi
      have := hB (Finset.univ.erase i) (by simp [Finset.ne_of_mem_erase hi |>.symm])
      simp only [one_mul]; exact this
    have := Finset.sum_le_sum h2
    simp only [Finset.sum_sub_distrib] at this
    linarith
  | total =>
    simp only [g64e_total]
    have e1 : ∑ j, w j * ((∑ i, cH (r j) {i}) - cH (r j) Finset.univ)
        = (∑ i, A {i}) - A Finset.univ := by
      simp only [hAdef, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
    rw [e1, hsplit, hsplit]
    have h1 := hB {π} (Finset.mem_singleton_self _)
    have h2 : ∀ i ∈ Finset.univ.erase π, A {i} ≤ cH p {i} := by
      intro i hi
      exact hA {i} (by simp [Finset.ne_of_mem_erase hi |>.symm])
    have := Finset.sum_le_sum h2
    linarith

end cmmono3

section cmrest
open Classical

def psv204_split {S : Type} (d1 d2 : S → ℕ) :
    ((i : S) → Fin (d1 i * d2 i)) ≃ ((i : S) → Fin (d1 i)) × ((i : S) → Fin (d2 i)) where
  toFun F := (fun i => (finProdFinEquiv.symm (F i)).1, fun i => (finProdFinEquiv.symm (F i)).2)
  invFun z i := finProdFinEquiv (z.1 i, z.2 i)
  left_inv F := by funext i; exact finProdFinEquiv.apply_symm_apply (F i)
  right_inv z := by ext i <;> simp

theorem cm_nonneg {n : ℕ} (hn : 2 ≤ n) (kind : InformationKind) (p : CData n)
    (hp : IsValidClassicalData p) : 0 ≤ cValue kind p := by
  cases kind with
  | dual => rw [g64e_S3 hn p hp]; exact Finset.sum_nonneg fun i _ => g64e_cmi_nonneg p hp _ _ _
  | total => rw [g64e_T1 hn p hp]; exact Finset.sum_nonneg fun i _ => g64e_cmi_nonneg p hp _ _ _

theorem cm_indep_M {n : ℕ} (p : CData n) (q : (i : Fin n) → Fin (p.dims i) → ℝ)
    (hq : ∀ i, IsLaw (q i)) (hx : ∀ x, p.prob x = ∏ i, q i (x i)) (S : Finset (Fin n))
    (y : ClassicalBasis p.dims) :
    g64e_M p S y = ∏ i, (if i ∈ S then q i (y i) else 1) := by
  have h1 : ∀ i, (if i ∈ S then q i (y i) else 1) =
      ∑ a, (if i ∈ S then (if a = y i then q i a else 0) else q i a) := by
    intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi, (hq i).2]
  simp only [h1]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  unfold g64e_M g64e_ag
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hx]
  by_cases h : ∀ i ∈ S, x i = y i
  · rw [if_pos h]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S
    · simp [hi, h i hi]
    · simp [hi]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hne⟩ := h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hne])

theorem cm_indep_H {n : ℕ} (p : CData n) (hp : IsValidClassicalData p)
    (q : (i : Fin n) → Fin (p.dims i) → ℝ)
    (hq : ∀ i, IsLaw (q i)) (hx : ∀ x, p.prob x = ∏ i, q i (x i)) (S : Finset (Fin n)) :
    cH p S = ∑ i, if i ∈ S then -∑ y, p.prob y * Real.logb 2 (q i (y i)) else 0 := by
  rw [g64e_entropy]
  simp only [cm_indep_M p q hq hx]
  have hterm : ∀ y, p.prob y * Real.logb 2 (∏ i, (if i ∈ S then q i (y i) else 1)) =
      ∑ i, if i ∈ S then p.prob y * Real.logb 2 (q i (y i)) else 0 := by
    intro y
    rcases (hp.2.1 y).lt_or_eq with h | h
    · have hne : ∀ i, q i (y i) ≠ 0 := by
        intro i h0
        rw [hx, Finset.prod_eq_zero (Finset.mem_univ i) h0] at h
        exact lt_irrefl _ h
      rw [Real.logb_prod _ _ (fun i _ => by split_ifs <;> simp [hne]), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · rw [← h]; simp
  simp only [hterm]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem cm_indep {n : ℕ} (hn : 2 ≤ n) (kind : InformationKind) (p : CData n)
    (hp : IsValidClassicalData p) (hi : IsIndependentLaw p) : cValue kind p = 0 := by
  obtain ⟨q, hq, hx⟩ := hi
  set h : Fin n → ℝ := fun i => -∑ y, p.prob y * Real.logb 2 (q i (y i))
  have hH : ∀ S, cH p S = ∑ i, if i ∈ S then h i else 0 := cm_indep_H p hp q hq hx
  cases kind with
  | dual =>
    rw [g64e_dual]
    simp only [hH, Finset.mem_univ, if_true, Finset.mem_erase]
    rw [Finset.sum_comm]
    have : ∀ l : Fin n, ∑ i : Fin n, (if l ≠ i ∧ True then h l else 0) = (n - 1 : ℕ) * h l := by
      intro l
      simp only [and_true]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      congr 2
      rw [Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    simp only [this, Finset.mul_sum, sub_self]
  | total =>
    rw [g64e_total]
    simp only [hH, Finset.mem_univ, if_true, Finset.mem_singleton]
    rw [Finset.sum_comm]
    simp

theorem cm_equiv {Ω Ω' V : Type*} [Fintype Ω] [Fintype Ω'] (e : Ω' ≃ Ω) (P : Ω → ℝ) (f : Ω → V) :
    cmH (fun ω => P (e ω)) (fun ω => f (e ω)) = cmH P f := by
  unfold cmH cmM
  congr 1
  have : ∀ ω', (∑ ω'', if f (e ω'') = f (e ω') then P (e ω'') else 0) =
      ∑ ω, if f ω = f (e ω') then P ω else 0 := fun ω' =>
    Equiv.sum_comp e (fun ω => if f ω = f (e ω') then P ω else 0)
  simp only [this]
  exact Equiv.sum_comp e (fun ω => P ω * Real.logb 2 (∑ ω'', if f ω'' = f ω then P ω'' else 0))

theorem cm_cH_prod {n : ℕ} (p q : CData n) (hp : IsValidClassicalData p)
    (hq : IsValidClassicalData q) (S : Finset (Fin n)) :
    cH (cProduct p q) S = cH p S + cH q S := by
  rw [cm_cH, cm_cH, cm_cH]
  rw [cm_H_congr (cProduct p q).prob (cmV S)
    (fun x => (fun z : ClassicalBasis p.dims × ClassicalBasis q.dims => (cmV S z.1, cmV S z.2))
      (psv204_split p.dims q.dims x))]
  · exact (cm_equiv (psv204_split p.dims q.dims)
      (fun z : ClassicalBasis p.dims × ClassicalBasis q.dims => p.prob z.1 * q.prob z.2)
      (fun z : ClassicalBasis p.dims × ClassicalBasis q.dims => (cmV S z.1, cmV S z.2))).trans
      (cm_prod _ _ hp.2.1 hq.2.1 hp.2.2 hq.2.2 _ _)
  · intro x y
    simp only [Prod.mk.injEq, cmV_eq, psv204_split, Equiv.coe_fn_mk]
    constructor
    · intro h
      exact ⟨fun i hi => by rw [h i hi], fun i hi => by rw [h i hi]⟩
    · rintro ⟨h1, h2⟩ i hi
      exact finProdFinEquiv.symm.injective (Prod.ext (h1 i hi) (h2 i hi))

theorem cm_add {n : ℕ} (kind : InformationKind) (p q : CData n) (hp : IsValidClassicalData p)
    (hq : IsValidClassicalData q) : cValue kind (cProduct p q) = cValue kind p + cValue kind q := by
  cases kind with
  | dual =>
    simp only [g64e_dual, cm_cH_prod p q hp hq, Finset.sum_add_distrib]; ring
  | total =>
    simp only [g64e_total, cm_cH_prod p q hp hq, Finset.sum_add_distrib]; ring

theorem cm_cH_cont {n : ℕ} (d : Fin n → ℕ) (S : Finset (Fin n)) :
    Continuous (fun P : {P : ClassicalBasis d → ℝ // IsLaw P} => cH ⟨d, P.val⟩ S) := by
  unfold cH shannon
  have hf : Continuous (fun t : ℝ => t * Real.logb 2 t) := by
    have : (fun t : ℝ => t * Real.logb 2 t) = fun t => (t * Real.log t) / Real.log 2 := by
      funext t; simp [Real.logb, mul_div_assoc]
    rw [this]; exact Real.continuous_mul_log.div_const _
  apply Continuous.neg
  show Continuous fun P : {P : ClassicalBasis d → ℝ // IsLaw P} =>
    ∑ a : ((i : {i // i ∈ S}) → Fin (d i.val)),
      lawMarginal ⟨d, P.val⟩ S a * Real.logb 2 (lawMarginal ⟨d, P.val⟩ S a)
  refine continuous_finsetSum (M := ℝ) _ fun a _ => ?_
  refine hf.comp ?_
  show Continuous fun P : {P : ClassicalBasis d → ℝ // IsLaw P} =>
    ∑ x : ClassicalBasis d, if (∀ i : {i // i ∈ S}, x i.val = a i) then P.val x else 0
  refine continuous_finsetSum (M := ℝ) (X := {P : ClassicalBasis d → ℝ // IsLaw P}) _ fun x _ => ?_
  by_cases h : ∀ i : {i // i ∈ S}, x i.val = a i
  · exact ((continuous_apply (A := fun _ : ClassicalBasis d => ℝ) x).comp
      continuous_subtype_val).congr fun P => (if_pos h).symm
  · exact continuous_const.congr fun P => (if_neg h).symm

theorem cm_cont {n : ℕ} (kind : InformationKind) (d : Fin n → ℕ) :
    Continuous (fun P : {P : ClassicalBasis d → ℝ // IsLaw P} => cValue kind ⟨d, P.val⟩) := by
  cases kind with
  | dual =>
    simp only [g64e_dual]
    exact (continuous_finsetSum _ fun i _ => cm_cH_cont d _).sub
      (continuous_const.mul (cm_cH_cont d _))
  | total =>
    simp only [g64e_total]
    exact (continuous_finsetSum _ fun i _ => cm_cH_cont d _).sub (cm_cH_cont d _)

end cmrest

section cmperm
open Classical

theorem cm_perm_cH {n : ℕ} (p : CData n) (e : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    cH (permuteData p e) S = cH p (S.map e.toEmbedding) := by
  let φ := Equiv.piCongrLeft (fun k => Fin (p.dims k)) e
  have hφ : ∀ (y : ClassicalBasis (permuteData p e).dims) (a : Fin n), φ y (e a) = y a :=
    fun y a => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hprob : ∀ y, (permuteData p e).prob y = p.prob (φ y) := by
    intro y
    show p.prob _ = _
    congr 1
    funext i
    apply Fin.ext
    have hv : ∀ j a, j = e a → (φ y j).val = (y a).val := by
      intro j a h; subst h; rw [hφ]
    rw [hv i (e.symm i) (e.apply_symm_apply i).symm]; rfl
  rw [cm_cH, cm_cH]
  rw [cm_H_congr (permuteData p e).prob (cmV S) (fun y => cmV (S.map e.toEmbedding) (φ y))]
  · rw [show (permuteData p e).prob = fun y => p.prob (φ y) from funext hprob]
    exact cm_equiv φ p.prob (cmV (S.map e.toEmbedding))
  · intro x y
    rw [cmV_eq, cmV_eq]
    constructor
    · intro h k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hk
      simp only [Equiv.toEmbedding_apply]
      rw [hφ, hφ]; exact h a ha
    · intro h a ha
      have := h (e a) (by exact Finset.mem_map_of_mem _ ha)
      rwa [hφ, hφ] at this

theorem cm_perm {n : ℕ} (kind : InformationKind) (p : CData n) (e : Equiv.Perm (Fin n)) :
    cValue kind (permuteData p e) = cValue kind p := by
  have h1 : ∀ i, (Finset.univ.erase i).map e.toEmbedding = Finset.univ.erase (e i) := by
    intro i; ext j; simp [Equiv.toEmbedding_apply]
  have h2 : (Finset.univ : Finset (Fin n)).map e.toEmbedding = Finset.univ := by simp
  have h3 : ∀ i, ({i} : Finset (Fin n)).map e.toEmbedding = {e i} := by intro i; simp
  cases kind with
  | dual =>
    simp only [g64e_dual, cm_perm_cH, h1, h2]
    congr 1
    exact Equiv.sum_comp e (fun i => cH p (Finset.univ.erase i))
  | total =>
    simp only [g64e_total, cm_perm_cH, h3, h2]
    congr 1
    exact Equiv.sum_comp e (fun i => cH p {i})

end cmperm


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


section cmcopies
open Classical

theorem cm_pow {α V : Type*} [Fintype α] (P : α → ℝ) (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
    (f : α → V) : ∀ k : ℕ,
    cmH (fun x : Fin k → α => ∏ j, P (x j)) (fun x => fun j => f (x j)) = k * cmH P f
  | 0 => by
    rw [cm_H_congr _ _ (fun _ : Fin 0 → α => ()) (fun x y => by
      simp only [iff_true]; funext j; exact j.elim0), cm_H_const]
    · simp
    · simp
  | k + 1 => by
    have ih := cm_pow P hP hP1 f k
    let e := Fin.consEquiv (fun _ : Fin (k+1) => α)
    have h0 : ∀ y : Fin k → α, 0 ≤ ∏ j : Fin k, P (y j) := fun y => Finset.prod_nonneg fun j _ => hP _
    have h1 : ∑ y : Fin k → α, ∏ j : Fin k, P (y j) = 1 := by
      rw [← Fintype.prod_sum (fun _ : Fin k => P)]
      simp [hP1]
    have hprod := cm_prod P (fun y : Fin k → α => ∏ j, P (y j)) hP h0 hP1 h1 f
      (fun y => fun j => f (y j))
    rw [ih] at hprod
    have heq := cm_equiv e (fun x : Fin (k+1) → α => ∏ j, P (x j)) (fun x => fun j => f (x j))
    rw [← heq]
    have hP' : (fun y : α × (Fin k → α) => ∏ j, P (e y j)) =
        fun y => P y.1 * ∏ j : Fin k, P (y.2 j) := by
      funext y; rw [Fin.prod_univ_succ]; simp [e, Fin.consEquiv]
    rw [hP', cm_H_congr _ _ (fun y : α × (Fin k → α) => (f y.1, fun j => f (y.2 j)))]
    · rw [hprod]; push_cast; ring
    · intro x y
      simp only [Prod.mk.injEq, funext_iff, Fin.forall_fin_succ]
      simp [e, Fin.consEquiv]

def cmCE {n : ℕ} (p : CData n) (k : ℕ) :
    ClassicalBasis (cCopies p k).dims ≃ (Fin k → ClassicalBasis p.dims) :=
  (Equiv.piCongrRight fun i => (Fintype.equivFin (Fin k → Fin (p.dims i))).symm).trans
    (Equiv.piComm fun i j => Fin (p.dims i))

theorem cmCE_apply {n : ℕ} (p : CData n) (k : ℕ) (x : ClassicalBasis (cCopies p k).dims) (j i) :
    cmCE p k x j i = (Fintype.equivFin (Fin k → Fin (p.dims i))).symm (x i) j := rfl

theorem cm_cH_copies {n : ℕ} (p : CData n) (hp : IsValidClassicalData p) (k : ℕ)
    (S : Finset (Fin n)) : cH (cCopies p k) S = k * cH p S := by
  rw [cm_cH, cm_cH, ← cm_pow p.prob hp.2.1 hp.2.2 (cmV S) k, ← cm_equiv (cmCE p k)]
  apply cm_H_congr
  intro x y
  rw [cmV_eq, funext_iff]
  simp only [cmV_eq, cmCE_apply]
  constructor
  · intro h j i hi; rw [h i hi]
  · intro h i hi
    apply (Fintype.equivFin (Fin k → Fin (p.dims i))).symm.injective
    funext j; exact h j i hi

theorem cm_copies {n : ℕ} (kind : InformationKind) (p : CData n) (hp : IsValidClassicalData p)
    (k : ℕ) : cValue kind (cCopies p k) = k * cValue kind p := by
  cases kind with
  | dual => simp only [g64e_dual, cm_cH_copies p hp, ← Finset.mul_sum]; ring
  | total => simp only [g64e_total, cm_cH_copies p hp, ← Finset.mul_sum]; ring

theorem cm_sum_flatMap {α : Type*} (l : List α) (g : α → List ℝ) :
    (l.flatMap g).sum = (l.map fun a => (g a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem cm_lsum_mul {β : Type*} (l : List β) (c : ℝ) (g : β → ℝ) :
    (l.map fun z => c * g z).sum = c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, mul_add]

theorem cm_clopc {n : ℕ} (M : CData n → ℝ)
    (hM : ∀ (p : CData n) (k : ℕ) (w : Fin k → ℝ) (r : Fin k → CData n),
      CInstrument p w r → (∑ j, w j * M (r j)) ≤ M p)
    (p : CData n) (out : List (ℝ × CData n)) (h : CLOPC p out) :
    (∀ z ∈ out, 0 ≤ z.1) ∧ (out.map Prod.fst).sum = 1 ∧
      (out.map fun z => z.1 * M z.2).sum ≤ M p := by
  induction h with
  | stop p _ => simp
  | step p k w r hI next hn ih =>
    have hw := hI.2.1
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      simp only [List.mem_flatMap, List.mem_map] at hz
      obtain ⟨j, _, z', hz', rfl⟩ := hz
      exact mul_nonneg (hw.1 j) ((ih j).1 z' hz')
    · rw [List.map_flatMap, cm_sum_flatMap]
      simp only [List.map_map, Function.comp_def]
      have : ∀ j, ((next j).map fun z => w j * z.1).sum = w j := by
        intro j
        rw [cm_lsum_mul (next j) (w j) Prod.fst, (ih j).2.1, mul_one]
      simp only [this]
      rw [← Fin.sum_univ_def]; exact hw.2
    · rw [List.map_flatMap, cm_sum_flatMap]
      simp only [List.map_map, Function.comp_def]
      have : ∀ j, ((next j).map fun z => w j * z.1 * M z.2).sum =
          w j * ((next j).map fun z => z.1 * M z.2).sum := by
        intro j
        rw [← cm_lsum_mul]; simp only [mul_assoc]
      simp only [this]
      rw [← Fin.sum_univ_def]
      calc _ ≤ ∑ j, w j * M (r j) :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j).2.2 (hw.1 j)
        _ ≤ M p := hM p k w r hI

theorem cm_esc {n : ℕ} (M : CData n → ℝ)
    (hM : ∀ (p : CData n) (k : ℕ) (w : Fin k → ℝ) (r : Fin k → CData n),
      CInstrument p w r → (∑ j, w j * M (r j)) ≤ M p)
    (p q : CData n) (h : ExactSecretConversion p q) : M q ≤ M p := by
  obtain ⟨out, hout, hq⟩ := h
  obtain ⟨h0, h1, h2⟩ := cm_clopc M hM p out hout
  have : (out.map fun z => z.1 * M z.2) = out.map fun z => z.1 * M q := by
    apply List.map_congr_left
    intro z hz
    rcases (h0 z hz).lt_or_eq with h | h
    · rw [hq z hz h]
    · rw [← h, zero_mul, zero_mul]
  rw [this, show (out.map fun z => z.1 * M q) = out.map fun z => M q * z.1 from
    List.map_congr_left fun z _ => mul_comm _ _, cm_lsum_mul out (M q) Prod.fst, h1, mul_one] at h2
  exact h2

end cmcopies

theorem cm_vals : cValue .dual (exampleLaw 3) = 1 ∧ cValue .total (exampleLaw 3) = 2 ∧
    cValue .dual (exampleLaw 4) = 2 ∧ cValue .total (exampleLaw 4) = 1 := by
  have a := g64e_L3.2 3
  have b := g64e_L3.2 4
  have c := g64e_L4.2 3
  have d := g64e_L4.2 4
  simp [fiveValues, fiveTable] at a b c d
  exact ⟨a, b, c, d⟩

theorem cm_comb_mono (lambda : ℝ) (h0 : 0 ≤ lambda) (h1 : lambda ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    IsCMonotone (combination lambda : CData n → ℝ) := by
  have h1' : 0 ≤ 1 - lambda := by linarith
  refine ⟨fun p hp => ?_, fun p hp hi => ?_, fun p k w r h => ?_, fun p q hp hq => ?_, fun d _ => ?_⟩
  · unfold combination
    exact add_nonneg (mul_nonneg h0 (cm_nonneg hn _ p hp)) (mul_nonneg h1' (cm_nonneg hn _ p hp))
  · unfold combination
    rw [cm_indep hn _ p hp hi, cm_indep hn _ p hp hi]; ring
  · unfold combination
    have a := mul_le_mul_of_nonneg_left (cm_mono .dual p k w r h) h0
    have b := mul_le_mul_of_nonneg_left (cm_mono .total p k w r h) h1'
    have e : ∑ j, w j * (lambda * cValue .dual (r j) + (1 - lambda) * cValue .total (r j)) =
        lambda * ∑ j, w j * cValue .dual (r j) + (1 - lambda) * ∑ j, w j * cValue .total (r j) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]; linarith
  · unfold combination
    rw [cm_add _ p q hp hq, cm_add _ p q hp hq]; ring
  · unfold combination
    exact (continuous_const.mul (cm_cont .dual d)).add (continuous_const.mul (cm_cont .total d))

theorem solution (lambda : ℝ) :
    ((0 ≤ lambda ∧ lambda ≤ 1) → ∀ n : ℕ, 2 ≤ n →
      IsCMonotone (combination lambda : CData n → ℝ)) ∧
    (IsCMonotone (combination lambda : CData 3 → ℝ) ↔
      0 ≤ lambda ∧ lambda ≤ 1) := by
  refine ⟨fun h n hn => cm_comb_mono lambda h.1 h.2 n hn, ⟨fun hM => ?_,
    fun h => cm_comb_mono lambda h.1 h.2 3 (by norm_num)⟩⟩
  obtain ⟨v1, v2, v3, v4⟩ := cm_vals
  obtain ⟨c1, c2⟩ := QAlgorithms.Papers.Independent.Renew46.P37.twoCopyConversions
  have a := cm_esc _ hM.2.2.1 _ _ c1
  have b := cm_esc _ hM.2.2.1 _ _ c2
  unfold combination at a b
  rw [cm_copies _ _ g64e_L3.1, cm_copies _ _ g64e_L3.1, v1, v2, v3, v4] at a
  rw [cm_copies _ _ g64e_L4.1, cm_copies _ _ g64e_L4.1, v1, v2, v3, v4] at b
  push_cast at a b
  constructor <;> linarith
