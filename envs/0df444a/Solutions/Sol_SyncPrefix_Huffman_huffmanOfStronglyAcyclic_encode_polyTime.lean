-- Prove2me | solution 1 for SyncPrefix.Huffman.huffmanOfStronglyAcyclic_encode_polyTime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:39:38.126836+00:00
-- url     : https://prove2.me/submissions/b6ae6f24-4da7-4131-be54-b655f19e1580
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_SyncPrefix_Huffman_Lemma5Construction
import Definitions.Def_SyncPrefix_Huffman_AutomatonCodec
import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_SyncPrefix_Huffman_huffmanEncodeMap_polyTime

open SyncPrefix.Huffman

private lemma readUnaryOpt_replicate (m : ℕ) (rest : List (Option Bool)) :
    readUnaryOpt (List.replicate m (some true) ++ none :: rest) = (m, rest) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [List.replicate_succ, readUnaryOpt, ih]

private lemma readUnaryList_flatMap (L : List ℕ) (rest : List (Option Bool)) :
    readUnaryList L.length
      ((L.flatMap fun m => List.replicate m (some true) ++ [none]) ++ rest) = (L, rest) := by
  induction L with
  | nil => rfl
  | cons m L ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, List.cons_append,
      List.nil_append, readUnaryList, readUnaryOpt_replicate, ih]

private lemma my_getD_eq_getElem {α : Type} :
    ∀ (xs : List α) (i : ℕ) (d : α) (h : i < xs.length), xs.getD i d = xs[i]
  | [], i, _, h => absurd h (Nat.not_lt_zero i)
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, i + 1, d, h => my_getD_eq_getElem xs i d (Nat.lt_of_succ_lt_succ h)

private lemma my_getD_append_left {α : Type} :
    ∀ (xs ys : List α) (i : ℕ) (d : α) (_ : i < xs.length),
      (xs ++ ys).getD i d = xs.getD i d
  | [], _, i, _, h => absurd h (Nat.not_lt_zero i)
  | _ :: _, _, 0, _, _ => rfl
  | _ :: xs, ys, i + 1, d, h => my_getD_append_left xs ys i d (Nat.lt_of_succ_lt_succ h)

private lemma my_getD_append_right {α : Type} :
    ∀ (xs ys : List α) (i : ℕ) (d : α) (_ : xs.length ≤ i),
      (xs ++ ys).getD i d = ys.getD (i - xs.length) d
  | [], ys, i, d, _ => by simp
  | _ :: xs, ys, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: xs, ys, i + 1, d, h => by
    simp only [List.cons_append, List.getD_cons_succ, List.length_cons, Nat.succ_sub_succ_eq_sub]
    exact my_getD_append_right xs ys i d (Nat.le_of_succ_le_succ h)

private lemma length_flatMap_finRange {n k : ℕ} (g : Fin n → Fin k → ℕ) (xs : List (Fin n)) :
    (xs.flatMap fun q => (List.finRange k).map (g q)).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons q xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_finRange,
      List.length_cons, ih]
    ring

private lemma getD_map_finRange {k : ℕ} (f : Fin k → ℕ) (a : Fin k) :
    ((List.finRange k).map f).getD a.val 0 = f a := by
  have hlt : a.val < ((List.finRange k).map f).length := by
    simp [a.isLt]
  rw [my_getD_eq_getElem _ _ _ hlt, List.getElem_map, List.getElem_finRange]
  simp

private lemma getD_flatMap_finRange {n k : ℕ} (g : Fin n → Fin k → ℕ) :
    ∀ (xs : List (Fin n)) (i : ℕ) (hi : i < xs.length) (a : Fin k),
      (xs.flatMap fun q => (List.finRange k).map (g q)).getD (i * k + a.val) 0 =
        g (xs[i]) a
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero i)
  | q₀ :: xs, 0, _, a => by
    simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
    rw [my_getD_append_left _ _ _ _ (by simp [a.isLt])]
    exact getD_map_finRange (g q₀) a
  | q₀ :: xs, i + 1, hi, a => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    have hge : ((List.finRange k).map (g q₀)).length ≤ (i + 1) * k + a.val := by
      simp only [List.length_map, List.length_finRange]
      nlinarith
    rw [my_getD_append_right _ _ _ _ hge]
    simp only [List.length_map, List.length_finRange]
    have heq : (i + 1) * k + a.val - k = i * k + a.val := by
      rw [Nat.add_mul, one_mul]
      omega
    rw [heq]
    exact getD_flatMap_finRange g xs i (Nat.lt_of_succ_lt_succ hi) a

private lemma decodeAutomaton_of_parts (w : List (Option Bool)) (n k : ℕ)
    (w₁ w₂ : List (Option Bool)) (table : List ℕ) (rest : List (Option Bool))
    (h₁ : readUnaryOpt w = (n, w₁))
    (h₂ : readUnaryOpt w₁ = (k, w₂))
    (h₃ : readUnaryList (n * k) w₂ = (table, rest)) :
    decodeAutomaton w =
      { n := n
        k := k
        δ := fun q a =>
          let v := table.getD (q.val * k + a.val) 0
          if h : v < n then ⟨v, h⟩ else q } := by
  unfold decodeAutomaton
  rw [h₁]
  dsimp only
  rw [h₂]
  dsimp only
  rw [h₃]

private lemma decodeAutomaton_encode (A : Automaton) :
    decodeAutomaton A.encode = A := by
  let L : List ℕ := (List.finRange A.n).flatMap fun q =>
    (List.finRange A.k).map fun a => (A.δ q a).val
  let w₂ : List (Option Bool) :=
    (List.finRange A.n).flatMap fun q =>
      (List.finRange A.k).flatMap fun a => List.replicate (A.δ q a).val (some true) ++ [none]
  let w₁ : List (Option Bool) := List.replicate A.k (some true) ++ none :: w₂
  have henc : A.encode = List.replicate A.n (some true) ++ none :: w₁ := by
    simp [Automaton.encode, w₁, w₂, List.append_assoc]
  have h₁ : readUnaryOpt A.encode = (A.n, w₁) := by
    rw [henc, readUnaryOpt_replicate]
  have h₂ : readUnaryOpt w₁ = (A.k, w₂) := by
    dsimp [w₁]
    exact readUnaryOpt_replicate A.k w₂
  have hL_len : L.length = A.n * A.k := by
    dsimp [L]
    rw [length_flatMap_finRange, List.length_finRange]
  have hL_flat : (L.flatMap fun m => List.replicate m (some true) ++ [none]) = w₂ := by
    dsimp [L, w₂]
    induction (List.finRange A.n) with
    | nil => rfl
    | cons q qs ih =>
      simp [List.flatMap_cons, List.flatMap_append, List.flatMap_map, ih]
  have h₃ : readUnaryList (A.n * A.k) w₂ = (L, []) := by
    rw [← hL_flat, ← hL_len]
    simpa using readUnaryList_flatMap L []
  rw [decodeAutomaton_of_parts A.encode A.n A.k w₁ w₂ L [] h₁ h₂ h₃]
  cases A with
  | mk n k δ =>
    dsimp only at L ⊢
    congr
    funext q a
    have hget : L.getD (q.val * k + a.val) 0 = (δ q a).val := by
      have h := getD_flatMap_finRange (fun q' a' => (δ q' a').val)
        (List.finRange n) q.val (by simp [q.isLt]) a
      simpa [L] using h
    rw [hget, dif_pos (δ q a).isLt]

theorem solution :
    ∃ f : List (Option Bool) → List (Option Bool), CookPvsNP.PolyTimeComputable f ∧
      ∀ A : Automaton, StronglyAcyclic A.δ → IsSynchronizing A.δ →
        f A.encode = (huffmanOfStronglyAcyclic A).encode := by
  refine ⟨huffmanEncodeMap, huffmanEncodeMap_polyTime, fun A _ _ => ?_⟩
  unfold huffmanEncodeMap
  rw [decodeAutomaton_encode]
