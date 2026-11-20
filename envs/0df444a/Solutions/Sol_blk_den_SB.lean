-- Prove2me | solution 1 for blk_den_SB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:11:17.051179+00:00
-- url     : https://prove2.me/submissions/5d2284f5-38bc-43a2-8acc-f4ad5a5a2a7d

module
public import Definitions.Def_ForbiddenMatrix_SmallPatterns
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Nat.Choose.Basic
public import Definitions.Def_ForbiddenMatrix_Mathlib_Data_ZMod_Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Qify
public import Definitions.Def_ForbiddenMatrix_PermutationPatterns
public import Theorems.Thm_permPattern_one
public import Theorems.Thm_permPattern_refl
public import Theorems.Thm_Fin_natCast_val_eq_zmodFinEquiv
public import Theorems.Thm_card_interval
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_ex_identityPattern_two
public import Theorems.Thm_ex_zero
attribute [local simp] Fin.natCast_val_eq_zmodFinEquiv
attribute [local simp] card_rectPtSet
attribute [local simp] card_rectPtsetSubsetMatrix
attribute [local simp] contains_of_isEmpty
attribute [local simp] ex_identityPattern_two
attribute [local simp] ex_zero


attribute [local simp] permPattern_one
attribute [local simp] permPattern_refl
section
@[expose] public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
@[simp] private lemma le_mul_div_add_one {n q : ℕ} (p : Fin n) (h : 0 < q) : p < q * (p / q + 1) := by
  rw [Nat.mul_comm]
  exact Nat.lt_mul_of_div_lt (Nat.lt_add_one _) h
@[simp] private lemma card_intervalq (n q i : ℕ) (hn : 0 < n) (hq : q ∣ n) (h : i < n / q) :
    #{a : Fin n | ↑a ∈ Finset.Ico (q * ↑i) (q * (↑i + 1))} = q := by
  have hy : q * (i + 1) ≤ n := by
    observe h1 : q * (n / q - 1) = q * (n / q) - q
    observe h2 : q * (n / q) = n
    observe : i ≤ n / q - 1
    observe h3 : q * i ≤ q * (n / q - 1)
    calc
          q * (i+1)
      _ = q * i + q := rfl
      _ ≤ q * (n / q -1) + q := Nat.add_le_add_right h3 q
      _ = (q * (n / q) - q) + q := Nat.add_right_cancel_iff.mpr h1
      _ = n := by
        rw [h2]
        have : n - q + q = n + q - q := by
          have := Nat.le_of_dvd hn hq
          lia
        rw [this]
        exact Eq.symm (Nat.eq_sub_of_add_eq rfl)
  calc
     #{a : Fin n | ↑a ∈ Finset.Ico (q * ↑i) (q * (↑i + 1))}
      = #(.Ico (q * ↑i) (q * (↑i + 1))) := card_interval (q * i) (q * (i + 1)) hy
     _ = (q * (↑i + 1)) - (q * ↑i) := Nat.card_Ico (q * i) (q * (i + 1))
     _ = q := Nat.sub_eq_of_eq_add' rfl
@[simp] private lemma card_rectPtsetq (n q i j : ℕ) (hq : q ∣ n) (h : i < n / q ∧ j < n / q) :
    #(rectPtsetq n q i j) = q * q := by
  simp only [rectPtsetq]
  convert card_rectPtSet n (q * i) (q * (i+1)) (q * j) (q * (j+1)) _
  · exact Nat.eq_sub_of_add_eq' rfl
  · exact Nat.eq_sub_of_add_eq' rfl
  obtain ⟨hi, hj⟩ := h
  constructor
  · calc
      q * (i+1) ≤ q * (n / q) := Nat.mul_le_mul_left q hi
      _     = n    := Nat.mul_div_cancel' hq
  · calc
      q * (j+1) ≤ q * (n / q) := Nat.mul_le_mul_left q hj
      _     = n    := Nat.mul_div_cancel' hq
set_option backward.isDefEq.respectTransparency false in
@[simp] private lemma card_rectPtsetqMatrix (M : Fin n → Fin n → Prop) (hq : q ∣ n) (i j : ℕ)
    (h : i < n / q ∧ j < n / q) : #(rectPtsetqMatrix M q i j) ≤ q * q := by
  calc
    #(rectPtsetqMatrix M q i j)
    _ ≤ #(rectPtsetq n q i j) := ?_
    _ = q * q := card_rectPtsetq n q i j hq h
  -- proof of the claim
  refine Finset.card_le_card ?_
  simp only [rectPtsetqMatrix, rectPtsetq, Prod.mk.eta]
  intro p h
  simp only [mem_filter, Finset.mem_univ, true_and] at h
  exact h.2
@[simp] private lemma p_to_pq {p : Fin n × Fin n} (hq : q ≠ 0) :
    p ∈ rectPtset n (q * (p.1 / q)) (q * (p.1 / q + 1)) (q * (p.2 / q)) (q * (p.2 / q + 1)) := by
  simp only [rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ, true_and]
  constructor <;> exact ⟨Nat.mul_div_le .., le_mul_div_add_one _ <| by lia⟩
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {n : ℕ} (k : ℕ) (M : Fin n → Fin n → Prop) :
    let q := k ^ 2
    let B := blkMatrix M q
    let W (i j : Fin (n / q)) : Prop := k ≤ #{c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j}
    let T (i j : Fin (n / q)) : Prop := k ≤ #{r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}
    let S : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ ¬ W i j ∧ ¬ T i j
    let SB : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ S i j ∧ B i j
    ∀ (i j : Fin (n / q)), SB i j → blk_den M i j ≤ (k - 1) ^ 2 := by
  extract_lets q B W T S SB
  intro i j hij
  simp only [blk_den]
  simp only [ge_iff_le, not_le, blkMatrix, Prod.exists, SB, S, W, T, B] at hij
  obtain ⟨⟨num_cols, num_rows⟩, _⟩ := hij
  let R := (filter (fun r ↦ ∃ c, (r, c) ∈ rectPtsetqMatrix M q ↑i ↑j) Finset.univ)
  let C := (filter (fun c ↦ ∃ r, (r, c) ∈ rectPtsetqMatrix M q ↑i ↑j) Finset.univ)
  have rc : #R ≤ k - 1 := Nat.le_sub_one_of_lt num_rows
  have cc : #C ≤ k - 1 := Nat.le_sub_one_of_lt num_cols
  suffices (rectPtsetSubsetMatrix M R C) = rectPtsetqMatrix M q ↑i ↑j by
    rw [← this]
    calc
          #(rectPtsetSubsetMatrix M R C)
        ≤ #R * #C := card_rectPtsetSubsetMatrix M R C
      _ ≤ (k - 1) * (k - 1) := Nat.mul_le_mul rc cc
      _ = (k - 1) ^ 2 := by rw [sq]
  show (rectPtsetSubsetMatrix M R C) = rectPtsetqMatrix M q ↑i ↑j
  · ext
    simp only [rectPtsetSubsetMatrix, Prod.mk.eta, mem_product, mem_filter,
      Finset.mem_univ, true_and, rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico,
      and_congr_right_iff]
    intro hx
    simp only [rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, Prod.mk.eta,
      mem_product, mem_filter, Finset.mem_univ, true_and, R, C]
    aesop
