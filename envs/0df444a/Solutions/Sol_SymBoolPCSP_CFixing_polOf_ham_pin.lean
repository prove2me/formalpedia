-- Prove2me | solution 1 for SymBoolPCSP.CFixing.polOf_ham_pin
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:39:52.550208+00:00
-- url     : https://prove2.me/submissions/05a24009-23a2-496a-983c-1c80d82c5e42

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_claim_4_2
import Theorems.Thm_SymBoolPCSP_CFixing_claim_4_4

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_polOf_ham_pin

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem ham_congr {k : ℕ} {X Y : Set ℕ} (h : ∀ l ≤ k, l ∈ X ↔ l ∈ Y) : Ham k X = Ham k Y := by
  ext x; exact h _ (hw_le' x)

theorem polOf_mono {k L : ℕ} {P Q P' Q' : Set (Fin k → Bool)} {f : (Fin L → Bool) → Bool}
    (hf : PolOf P Q f) (hP : P' ⊆ P) (hQ : Q ⊆ Q') : PolOf P' Q' f :=
  fun M hM => hQ (hf M (fun l => hP (hM l)))

theorem polOf_ham_drop {L : ℕ} (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f) :
    ∀ (i n : ℕ) (S T : Set ℕ), S ⊆ T → T ⊆ Set.Iic (n + i) →
      PolOf (Ham (n + i) S) (Ham (n + i) T) f →
      PolOf (Ham n {l | l ∈ S ∧ l ≤ n}) (Ham n {l | l ∈ T ∧ l ≤ n}) f := by
  intro i
  induction i with
  | zero =>
    intro n S T _ hT hf
    rw [ham_congr (X := {l | l ∈ S ∧ l ≤ n}) (Y := S) (fun l hl => by simp [hl]),
      ham_congr (X := {l | l ∈ T ∧ l ≤ n}) (Y := T) (fun l hl => by simp [hl])]
    exact hf
  | succ i ih =>
    intro n S T hST hT hf
    have h2 := claim_4_2 (k := n + i + 1) (by omega) S T hST hT f hidem hf
    have h3 := ih n (S \ {n + i + 1}) (T \ {n + i + 1}) (Set.sdiff_subset_sdiff_left hST)
      (fun l hl => by
        have h1 := hT hl.1; have h2 : l ≠ n + i + 1 := hl.2
        simp only [Set.mem_Iic] at h1 ⊢; omega) h2
    rw [ham_congr (X := {l | l ∈ S ∧ l ≤ n}) (Y := {l | l ∈ S \ {n + i + 1} ∧ l ≤ n})
      (fun l hl => by simp <;> omega),
      ham_congr (X := {l | l ∈ T ∧ l ≤ n}) (Y := {l | l ∈ T \ {n + i + 1} ∧ l ≤ n})
      (fun l hl => by simp <;> omega)]
    exact h3

theorem polOf_ham_shift {L : ℕ} (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f)
    (hfold : IsFolded f) :
    ∀ (j n : ℕ) (S T : Set ℕ), S ⊆ T → T ⊆ Set.Iic (n + j) →
      PolOf (Ham (n + j) S) (Ham (n + j) T) f →
      PolOf (Ham n {l | l + j ∈ S}) (Ham n {l | l + j ∈ T}) f := by
  intro j
  induction j with
  | zero => intro n S T _ _ hf; simpa using hf
  | succ j ih =>
    intro n S T hST hT hf
    have h2 := claim_4_4 (k := n + j + 1) (by omega) S T hST hT f hidem hfold hf
    have h3 := ih n {l | l + 1 ∈ S} {l | l + 1 ∈ T} (fun l hl => hST hl)
      (fun l hl => by have := hT hl; simp only [Set.mem_Iic] at this ⊢; omega) h2
    have e : ∀ X : Set ℕ, {l | l + j ∈ {l | l + 1 ∈ X}} = {l | l + (j + 1) ∈ X} := fun X => by
      ext l; simp only [Set.mem_setOf_eq]; rw [show l + j + 1 = l + (j + 1) by omega]
    rw [e, e] at h3; exact h3

end Aux_polOf_ham_pin

open Aux_polOf_ham_pin in
/-- Pinning coordinates of Hamming promise relations (Claims 4.2 and 4.4 iterated): for an idempotent folded `f`, if `f ∈ Pol(Ham_{n+j+i}(S), Ham_{n+j+i}(T))` with `S ⊆ T ⊆ {0,…,n+j+i}`, then `f ∈ Pol(Ham_n(S'), Ham_n(T'))` where `S' = {l ≤ n : l + j ∈ S}` and `T' = {l ≤ n : l + j ∈ T}` (fix `j` coordinates to `1` and `i` coordinates to `0`). -/
theorem polOf_ham_pin {n i j L : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic (n + j + i))
    (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f) (hfold : IsFolded f)
    (hf : PolOf (Ham (n + j + i) S) (Ham (n + j + i) T) f) :
    PolOf (Ham n {l | l + j ∈ S ∧ l ≤ n}) (Ham n {l | l + j ∈ T ∧ l ≤ n}) f := by
  have h1 := polOf_ham_drop f hidem i (n + j) S T hST hT hf
  have h2 := polOf_ham_shift f hidem hfold j n {l | l ∈ S ∧ l ≤ n + j} {l | l ∈ T ∧ l ≤ n + j}
    (fun l (hl : l ∈ S ∧ l ≤ n + j) => (⟨hST hl.1, hl.2⟩ : l ∈ T ∧ l ≤ n + j))
    (fun l (hl : l ∈ T ∧ l ≤ n + j) => (hl.2 : l ≤ n + j)) h1
  rw [ham_congr (X := {l | l + j ∈ S ∧ l ≤ n}) (Y := {l | l + j ∈ {l | l ∈ S ∧ l ≤ n + j}})
    (fun l hl => by simp <;> omega),
    ham_congr (X := {l | l + j ∈ T ∧ l ≤ n}) (Y := {l | l + j ∈ {l | l ∈ T ∧ l ≤ n + j}})
    (fun l hl => by simp <;> omega)]
  exact h2

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {n i j L : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic (n + j + i))
    (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f) (hfold : IsFolded f)
    (hf : PolOf (Ham (n + j + i) S) (Ham (n + j + i) T) f) :
    PolOf (Ham n {l | l + j ∈ S ∧ l ≤ n}) (Ham n {l | l + j ∈ T ∧ l ≤ n}) f :=
  SymBoolPCSP.CFixing.polOf_ham_pin hST hT f hidem hfold hf
