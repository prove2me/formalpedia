-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.dickeTwoQubitMarginal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:42:15.969339+00:00
-- url     : https://prove2.me/submissions/7b803335-68fe-481b-b565-0f290a2f6fda

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

namespace X8P22D
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

abbrev S2 {n : ℕ} (a b : Fin n) := {t : Fin n // t ≠ a ∧ t ≠ b}

def E2 {n : ℕ} (a b : Fin n) (p : Bool × Bool) (z : S2 a b → Bool) : Fin n → Bool :=
  fun t => if t = a then p.1 else if h' : t = b then p.2 else
    if h : t = a then p.1 else z ⟨t, h, h'⟩

def res2 {n : ℕ} (a b : Fin n) (x : Fin n → Bool) : S2 a b → Bool := fun t => x t.1

theorem x8_E_a {n : ℕ} (a b : Fin n) (p) (z : S2 a b → Bool) : E2 a b p z a = p.1 := by
  simp [E2]

theorem x8_E_b {n : ℕ} {a b : Fin n} (hab : a ≠ b) (p) (z : S2 a b → Bool) : E2 a b p z b = p.2 := by
  simp [E2, Ne.symm hab]

theorem x8_E_res {n : ℕ} {a b : Fin n} (p) (z : S2 a b → Bool) : res2 a b (E2 a b p z) = z := by
  funext t
  simp [res2, E2, t.2.1, t.2.2]

theorem x8_res_E {n : ℕ} {a b : Fin n} (x : Fin n → Bool) :
    E2 a b (x a, x b) (res2 a b x) = x := by
  funext t
  unfold E2 res2
  by_cases h1 : t = a
  · subst h1; simp
  · by_cases h2 : t = b
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem x8_tqm {n : ℕ} {a b : Fin n} (hab : a ≠ b) (ρ : Op (Qubits n)) (p q : Bool × Bool) :
    twoQubitMarginal ρ a b p q = ∑ z : S2 a b → Bool, ρ (E2 a b p z) (E2 a b q z) := by
  unfold twoQubitMarginal
  have hin : ∀ x : Fin n → Bool, (∑ y : Qubits n, if x a = p.1 ∧ x b = p.2 ∧ y a = q.1 ∧ y b = q.2 ∧
      (∀ t, t ≠ a → t ≠ b → x t = y t) then ρ x y else 0) =
      if x a = p.1 ∧ x b = p.2 then ρ x (E2 a b q (res2 a b x)) else 0 := by
    intro x
    rw [Finset.sum_eq_single (E2 a b q (res2 a b x))]
    · have : ∀ t, t ≠ a → t ≠ b → x t = E2 a b q (res2 a b x) t := by
        intro t h1 h2; simp [E2, res2, h1, h2]
      by_cases h : x a = p.1 ∧ x b = p.2
      · rw [if_pos h, if_pos ⟨h.1, h.2, x8_E_a _ _ _ _, x8_E_b hab _ _, this⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]
    · intro y _ hy
      rw [if_neg]
      rintro ⟨-, -, h1, h2, h3⟩
      apply hy
      funext t
      by_cases ha : t = a
      · subst ha; rw [h1, x8_E_a]
      · by_cases hb : t = b
        · subst hb; rw [h2, x8_E_b hab]
        · rw [← h3 t ha hb]; simp [E2, res2, ha, hb]
    · simp
  simp only [hin]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun z => E2 a b p z) (fun x => res2 a b x)
  · intro z _; simp [x8_E_a, x8_E_b hab]
  · intro x _; simp
  · intro z _; exact x8_E_res p z
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have := x8_res_E (a := a) (b := b) x
    rw [hx.1, hx.2] at this
    exact this
  · intro z _; rw [x8_E_res]

def bn (b : Bool) : ℕ := if b then 1 else 0

theorem x8_hw_sum {ι : Type*} [Fintype ι] (x : ι → Bool) : hammingWeight x = ∑ t, bn (x t) := by
  unfold hammingWeight bn
  rw [Finset.card_filter]

theorem x8_wtE {n : ℕ} {a b : Fin n} (hab : a ≠ b) (p) (z : S2 a b → Bool) :
    hammingWeight (E2 a b p z) = bn p.1 + bn p.2 + hammingWeight z := by
  rw [x8_hw_sum, x8_hw_sum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have hb : b ∈ Finset.univ.erase a := by simp [Ne.symm hab]
  rw [← Finset.add_sum_erase _ _ hb, x8_E_a, x8_E_b hab, ← add_assoc]
  congr 1
  rw [Finset.sum_subtype (p := fun t => t ≠ a ∧ t ≠ b)]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [E2, t.2.1, t.2.2]
  · intro t; simp [and_comm]

theorem x8_cnt (T : Type) [Fintype T] [DecidableEq T] (s : ℕ) :
    (Finset.univ.filter (fun z : T → Bool => hammingWeight z = s)).card = (Fintype.card T).choose s := by
  rw [← Finset.card_univ, ← Finset.card_powersetCard]
  apply Finset.card_nbij' (fun z => Finset.univ.filter (fun t => z t = true)) (fun A t => decide (t ∈ A))
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hz⟩
  · intro A hA
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hA
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold hammingWeight
    rw [← hA.2]; congr 1; ext t; simp
  · intro z _; funext t; simp
  · intro A _; ext t; simp

theorem x8_cardS {n : ℕ} {a b : Fin n} (hab : a ≠ b) : Fintype.card (S2 a b) = n - 2 := by
  rw [Fintype.card_subtype]
  have : Finset.univ.filter (fun t : Fin n => t ≠ a ∧ t ≠ b) = Finset.univ \ {a, b} := by
    ext t; simp
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_pair hab, Finset.card_univ,
    Fintype.card_fin]

theorem x8_cc (C : ℕ) (hC : 0 < C) :
    ((Real.sqrt (C : ℝ))⁻¹ : ℂ) * conj ((Real.sqrt (C : ℝ))⁻¹ : ℂ) = (C : ℂ)⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  simp

theorem x8_val {n : ℕ} {a b : Fin n} (hab : a ≠ b) (r : ℕ) (hr : r ≤ n) (p q : Bool × Bool) :
    twoQubitMarginal (pureDensity (dicke (I := Fin n) r)) a b p q =
      if bn p.1 + bn p.2 = bn q.1 + bn q.2 ∧ bn p.1 + bn p.2 ≤ r then
        (((n-2).choose (r - (bn p.1 + bn p.2)) : ℕ) : ℂ) * ((n.choose r : ℕ) : ℂ)⁻¹ else 0 := by
  rw [x8_tqm hab]
  obtain ⟨P, hP⟩ : ∃ P, P = bn p.1 + bn p.2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = bn q.1 + bn q.2 := ⟨_, rfl⟩
  rw [← hP, ← hQ]
  have hs : ∀ z : S2 a b → Bool, pureDensity (dicke (I := Fin n) r) (E2 a b p z) (E2 a b q z) =
      if (P = Q ∧ P ≤ r) ∧ hammingWeight z = r - P then ((n.choose r : ℕ) : ℂ)⁻¹ else 0 := by
    intro z
    simp only [pureDensity, of_apply, dicke, x8_wtE hab, Fintype.card_fin, ← hP, ← hQ]
    by_cases h1 : P + hammingWeight z = r
    · by_cases h2 : Q + hammingWeight z = r
      · rw [if_pos h1, if_pos h2, if_pos ⟨⟨by omega, by omega⟩, by omega⟩]
        exact x8_cc _ (Nat.choose_pos hr)
      · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (by rw [← h.1.1]; exact h1))]; simp
    · rw [if_neg h1, zero_mul, if_neg (by rintro ⟨⟨h3, h4⟩, h5⟩; exact h1 (by omega))]
  rw [Finset.sum_congr rfl (fun z _ => hs z)]
  by_cases hPQ : P = Q ∧ P ≤ r
  · rw [if_pos hPQ, ← Finset.sum_filter]
    have : Finset.univ.filter (fun z : S2 a b → Bool => (P = Q ∧ P ≤ r) ∧ hammingWeight z = r - P) =
        Finset.univ.filter (fun z : S2 a b → Bool => hammingWeight z = r - P) := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hPQ, h⟩⟩
    rw [this, Finset.sum_const, x8_cnt, x8_cardS hab, nsmul_eq_mul]
  · simp only [hPQ, false_and, if_false, Finset.sum_const_zero]

theorem x8_k0 (N r : ℕ) (hr : r ≤ N + 2) :
    (N.choose r : ℂ) * ((N : ℂ) + 1) * ((N : ℂ) + 2) =
      ((N + 2).choose r : ℂ) * ((N : ℂ) + 2 - r) * ((N : ℂ) + 1 - r) := by
  rcases Nat.lt_or_ge N r with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    rcases (show r = N + 1 ∨ r = N + 2 by omega) with h' | h' <;> subst h' <;> push_cast <;> ring
  · have h1 := Nat.choose_mul_succ_eq N r
    have h2 := Nat.choose_mul_succ_eq (N + 1) r
    have e1 : (N.choose r : ℂ) * ((N : ℂ) + 1) = ((N + 1).choose r : ℂ) * ((N : ℂ) + 1 - r) := by
      have := congrArg (Nat.cast (R := ℂ)) h1
      push_cast [Nat.cast_sub (show r ≤ N + 1 by omega)] at this
      linear_combination this
    have e2 : ((N + 1).choose r : ℂ) * ((N : ℂ) + 2) = ((N + 2).choose r : ℂ) * ((N : ℂ) + 2 - r) := by
      have := congrArg (Nat.cast (R := ℂ)) h2
      push_cast [Nat.cast_sub (show r ≤ N + 1 + 1 by omega)] at this
      linear_combination this
    linear_combination ((N : ℂ) + 2) * e1 + ((N : ℂ) + 1 - r) * e2

theorem x8_k1 (N s : ℕ) (hr : s + 1 ≤ N + 2) :
    (N.choose s : ℂ) * ((N : ℂ) + 1) * ((N : ℂ) + 2) =
      ((N + 2).choose (s + 1) : ℂ) * ((s : ℂ) + 1) * ((N : ℂ) + 1 - s) := by
  have h1 := Nat.add_one_mul_choose_eq (N + 1) s
  have h2 := Nat.choose_mul_succ_eq N s
  have e1 : ((N : ℂ) + 2) * ((N + 1).choose s : ℂ) = ((N + 2).choose (s + 1) : ℂ) * ((s : ℂ) + 1) := by
    have := congrArg (Nat.cast (R := ℂ)) h1
    push_cast at this
    linear_combination this
  have e2 : (N.choose s : ℂ) * ((N : ℂ) + 1) = ((N + 1).choose s : ℂ) * ((N : ℂ) + 1 - s) := by
    have := congrArg (Nat.cast (R := ℂ)) h2
    push_cast [Nat.cast_sub (show s ≤ N + 1 by omega)] at this
    linear_combination this
  linear_combination ((N : ℂ) + 2) * e2 + ((N : ℂ) + 1 - s) * e1

theorem x8_k2 (N s : ℕ) :
    (N.choose s : ℂ) * ((N : ℂ) + 1) * ((N : ℂ) + 2) =
      ((N + 2).choose (s + 2) : ℂ) * ((s : ℂ) + 2) * ((s : ℂ) + 1) := by
  have h1 := Nat.add_one_mul_choose_eq N s
  have h2 := Nat.add_one_mul_choose_eq (N + 1) (s + 1)
  have e1 : ((N : ℂ) + 1) * (N.choose s : ℂ) = ((N + 1).choose (s + 1) : ℂ) * ((s : ℂ) + 1) := by
    have := congrArg (Nat.cast (R := ℂ)) h1
    push_cast at this
    linear_combination this
  have e2 : ((N : ℂ) + 2) * ((N + 1).choose (s + 1) : ℂ) = ((N + 2).choose (s + 2) : ℂ) * ((s : ℂ) + 2) := by
    have := congrArg (Nat.cast (R := ℂ)) h2
    push_cast at this
    linear_combination this
  linear_combination ((N : ℂ) + 2) * e1 + ((s : ℂ) + 1) * e2

theorem x8_L0 (n r : ℕ) (hn : 2 ≤ n) (hr : r ≤ n) :
    (((n - 2).choose r : ℕ) : ℂ) * ((n.choose r : ℕ) : ℂ)⁻¹ =
      ((n : ℂ) - r) * ((n : ℂ) - r - 1) / ((n : ℂ) * ((n : ℂ) - 1)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  have hC : ((N + 2).choose r : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
  have key := x8_k0 N r hr
  simp only [Nat.add_sub_cancel]
  push_cast
  have h1 : (N : ℂ) + 2 ≠ 0 := by norm_cast
  have h2 : (N : ℂ) + 2 - 1 ≠ 0 := by rw [show (N : ℂ) + 2 - 1 = ((N + 1 : ℕ) : ℂ) by push_cast; ring]; norm_cast
  field_simp
  linear_combination key

theorem x8_L1 (n r : ℕ) (hn : 2 ≤ n) (hr : r ≤ n) :
    (if 1 ≤ r then (((n - 2).choose (r - 1) : ℕ) : ℂ) * ((n.choose r : ℕ) : ℂ)⁻¹ else 0) =
      (r : ℂ) * ((n : ℂ) - r) / ((n : ℂ) * ((n : ℂ) - 1)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0; simp
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [if_pos (by omega)]
  have hC : ((N + 2).choose (s + 1) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
  have key := x8_k1 N s hr
  simp only [Nat.add_sub_cancel]
  push_cast
  have h1 : (N : ℂ) + 2 ≠ 0 := by norm_cast
  have h2 : (N : ℂ) + 2 - 1 ≠ 0 := by rw [show (N : ℂ) + 2 - 1 = ((N + 1 : ℕ) : ℂ) by push_cast; ring]; norm_cast
  field_simp
  linear_combination key

theorem x8_L2 (n r : ℕ) (hn : 2 ≤ n) (hr : r ≤ n) :
    (if 2 ≤ r then (((n - 2).choose (r - 2) : ℕ) : ℂ) * ((n.choose r : ℕ) : ℂ)⁻¹ else 0) =
      (r : ℂ) * ((r : ℂ) - 1) / ((n : ℂ) * ((n : ℂ) - 1)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  rcases (show r = 0 ∨ r = 1 ∨ 2 ≤ r by omega) with h0 | h0 | h0
  · subst h0; simp
  · subst h0; simp
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  rw [if_pos (by omega)]
  have hC : ((N + 2).choose (s + 2) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
  have key := x8_k2 N s
  simp only [Nat.add_sub_cancel]
  push_cast
  have h1 : (N : ℂ) + 2 ≠ 0 := by norm_cast
  have h2 : (N : ℂ) + 2 - 1 ≠ 0 := by rw [show (N : ℂ) + 2 - 1 = ((N + 1 : ℕ) : ℂ) by push_cast; ring]; norm_cast
  field_simp
  linear_combination key

theorem x8_n2 {n : ℕ} {a b : Fin n} (hab : a ≠ b) : 2 ≤ n := by
  rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
  have : a ≠ b := fun h => hab (Fin.ext h)
  omega

theorem x8_part1 {n : ℕ} {a b : Fin n} (hab : a ≠ b) (r : ℕ) (hr : r ≤ n) :
    twoQubitMarginal (pureDensity (dicke (I := Fin n) r)) a b = dickePairFormula n r := by
  ext p q
  rw [x8_val hab r hr]
  rcases p with ⟨_|_, _|_⟩ <;> rcases q with ⟨_|_, _|_⟩ <;>
    simp [bn, dickePairFormula, pureDensity, ket]
  all_goals first
    | exact x8_L0 n r (x8_n2 hab) hr
    | exact x8_L1 n r (x8_n2 hab) hr
    | exact x8_L2 n r (x8_n2 hab) hr

theorem x8_ent1 (n r : ℕ) : dickePairFormula n r (false, true) (true, false) =
    (r : ℂ) * ((n : ℂ) - r) / ((n : ℂ) * ((n : ℂ) - 1)) := by
  simp [dickePairFormula, pureDensity, ket]

theorem x8_ent2 (n r : ℕ) : dickePairFormula n r (false, true) (false, true) =
    (r : ℂ) * ((n : ℂ) - r) / ((n : ℂ) * ((n : ℂ) - 1)) := by
  simp [dickePairFormula, pureDensity, ket]

theorem x8_rest (n r : ℕ) (hn : 2 ≤ n) (hr : r ≤ n) :
    (0 < r → r < n → (dickePairFormula n r) (false,true) (true,false) ≠ 0) ∧
    (r = 0 → dickePairFormula n r = pureDensity (ket (false,false))) ∧
    (r = n → dickePairFormula n r = pureDensity (ket (true,true))) ∧
    dickePairFormula n r ≠ mixed (Bool × Bool) := by
  have hn0 : (n : ℂ) ≠ 0 := by norm_cast; omega
  have hn1 : (n : ℂ) - 1 ≠ 0 := by
    rw [show (n : ℂ) - 1 = ((n - 1 : ℕ) : ℂ) by push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; ring]
    norm_cast; omega
  refine ⟨fun h0 h1 => ?_, fun h0 => ?_, fun h0 => ?_, fun h => ?_⟩
  · rw [x8_ent1]
    have : (r : ℂ) ≠ 0 := by norm_cast; omega
    have : (n : ℂ) - r ≠ 0 := by
      rw [show (n : ℂ) - r = ((n - r : ℕ) : ℂ) by push_cast [Nat.cast_sub hr]; ring]
      norm_cast; omega
    exact div_ne_zero (mul_ne_zero ‹_› ‹_›) (mul_ne_zero hn0 hn1)
  · subst h0
    ext p q
    rcases p with ⟨_|_, _|_⟩ <;> rcases q with ⟨_|_, _|_⟩ <;>
      simp [dickePairFormula, pureDensity, ket, hn0, hn1]
  · subst h0
    ext p q
    rcases p with ⟨_|_, _|_⟩ <;> rcases q with ⟨_|_, _|_⟩ <;>
      simp [dickePairFormula, pureDensity, ket, hn0, hn1]
  · have e1 := congrFun (congrFun h (false, true)) (true, false)
    have e2 := congrFun (congrFun h (false, true)) (false, true)
    rw [x8_ent1] at e1
    rw [x8_ent2, e1] at e2
    simp [mixed] at e1 e2

end X8P22D

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22


open scoped ComplexConjugate ComplexOrder Matrix


local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

open QAlgorithms.Papers.Independent.Information100.P22 in
/-- Eq.(S70), PDF p.43: full formula, interior coherence, product endpoints, and nonuniformity. -/
theorem solution (m k r : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hr : r ≤ 2*(m*k)) (a b : Fin (2*(m*k))) (hab : a ≠ b) :
    twoQubitMarginal (pureDensity (dicke (I := Fin (2*(m*k))) r)) a b = dickePairFormula (2*(m*k)) r ∧
    (0 < r → r < 2*(m*k) → (dickePairFormula (2*(m*k)) r) (false,true) (true,false) ≠ 0) ∧
    (r = 0 → dickePairFormula (2*(m*k)) r = pureDensity (ket (false,false))) ∧
    (r = 2*(m*k) → dickePairFormula (2*(m*k)) r = pureDensity (ket (true,true))) ∧
    dickePairFormula (2*(m*k)) r ≠ mixed (Bool × Bool) :=
  by
  have hn : 2 ≤ 2*(m*k) := by
    have : 1 ≤ m * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  exact ⟨X8P22D.x8_part1 hab r hr, X8P22D.x8_rest _ r hn hr⟩



