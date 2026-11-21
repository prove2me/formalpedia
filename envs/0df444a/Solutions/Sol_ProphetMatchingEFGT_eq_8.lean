-- Prove2me | solution 1 for ProphetMatchingEFGT.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:29:40.473534+00:00
-- url     : https://prove2.me/submissions/98539b2a-199f-4e17-90c5-b609fd5f7ad7

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

open Finset

namespace Aux_ProphetMatchingEFGT_eq_8

open ProphetMatchingEFGT

lemma foldl_mem {α β : Type*} [DecidableEq α] (F : Finset α → α × β → Finset α)
    (hF : ∀ M p, ∀ y ∈ F M p, y = p.1 ∨ y ∈ M) (l : List (α × β)) (M : Finset α) (y : α)
    (hy : y ∈ l.foldl F M) : y ∈ M ∨ y ∈ l.map Prod.fst := by
  induction l generalizing M with
  | nil => left; simpa using hy
  | cons p l ih =>
    rw [List.foldl_cons] at hy
    rcases ih (F M p) hy with h | h
    · rcases hF M p y h with h' | h'
      · right
        rw [List.map_cons]
        exact List.mem_cons.mpr (Or.inl h')
      · left; exact h'
    · right
      rw [List.map_cons]
      exact List.mem_cons.mpr (Or.inr h)

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma bern_append (ps : List (Edge G × ℝ)) (e : Edge G) (a : ℝ)
    (f : List (Edge G × Bool) → ℝ) :
    bern (ps ++ [(e, a)]) f =
      bern ps (fun l => a * f (l ++ [(e, true)]) + (1 - a) * f (l ++ [(e, false)])) := by
  induction ps generalizing f with
  | nil => simp [bern]
  | cons p ps ih =>
    obtain ⟨e', b⟩ := p
    simp only [List.cons_append, bern, ih]

lemma bern_congr (ps : List (Edge G × ℝ)) (f g : List (Edge G × Bool) → ℝ)
    (h : ∀ l : List (Edge G × Bool), l.map Prod.fst = ps.map Prod.fst → f l = g l) :
    bern ps f = bern ps g := by
  induction ps generalizing f g with
  | nil =>
    simp only [bern]
    exact h [] rfl
  | cons p ps ih =>
    obtain ⟨e', b⟩ := p
    simp only [bern]
    rw [ih (fun l => f ((e', true) :: l)) (fun l => g ((e', true) :: l))
        (fun l hl => h _ (by simp [hl])),
      ih (fun l => f ((e', false) :: l)) (fun l => g ((e', false) :: l))
        (fun l hl => h _ (by simp [hl]))]

lemma bern_mul (ps : List (Edge G × ℝ)) (a : ℝ) (f : List (Edge G × Bool) → ℝ) :
    bern ps (fun l => a * f l) = a * bern ps f := by
  induction ps generalizing f with
  | nil => simp only [bern]
  | cons p ps ih =>
    obtain ⟨e', b⟩ := p
    simp only [bern]
    rw [ih, ih]
    ring

lemma map_fst_foldl (c : ℝ) (x : Edge G → ℝ) (es : List (Edge G)) (init : List (Edge G × ℝ)) :
    (es.foldl (fun ps e => ps ++ [(e, c / unmatchedProb ps e * x e)]) init).map Prod.fst =
      init.map Prod.fst ++ es := by
  induction es generalizing init with
  | nil => simp
  | cons a es ih =>
    rw [List.foldl_cons, ih]
    simp

lemma not_mem_greedy (l : List (Edge G × Bool)) (e : Edge G) (he : e ∉ l.map Prod.fst) :
    e ∉ greedy l := by
  intro h
  unfold greedy at h
  refine (foldl_mem _ (fun M p y hy => ?_) l ∅ e h).elim (fun h1 => by simp at h1) he
  try dsimp only at hy
  split_ifs at hy
  · exact Finset.mem_insert.mp hy
  · exact Or.inr hy

lemma greedy_false (l : List (Edge G × Bool)) (e : Edge G) :
    greedy (l ++ [(e, false)]) = greedy l := by
  unfold greedy
  rw [List.foldl_append]
  simp

lemma greedy_true (l : List (Edge G × Bool)) (e : Edge G) (hn : e ∉ greedy l) :
    e ∈ greedy (l ++ [(e, true)]) ↔ endsFree (greedy l) e := by
  unfold greedy at hn ⊢
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  try dsimp only
  split_ifs with hc
  · constructor
    · intro _
      exact hc.2
    · intro _
      exact Finset.mem_insert_self _ _
  · constructor
    · intro h
      exact (hn h).elim
    · intro h
      exact (hc ⟨rfl, h⟩).elim

lemma key (ps : List (Edge G × ℝ)) (e : Edge G) (a : ℝ) (hps : e ∉ ps.map Prod.fst) :
    prob (ps ++ [(e, a)]) (fun l => e ∈ greedy l) =
      a * prob ps (fun l => endsFree (greedy l) e) := by
  unfold prob
  rw [bern_append, ← bern_mul]
  apply bern_congr
  intro l hl
  try dsimp only
  have hn : e ∉ greedy l := not_mem_greedy l e (by rw [hl]; exact hps)
  simp only [greedy_false, if_neg hn, mul_zero, add_zero]
  congr 1
  by_cases hf : endsFree (greedy l) e
  · simp only [if_pos ((greedy_true l e hn).mpr hf), if_pos hf]
  · simp only [if_neg (fun h => hf ((greedy_true l e hn).mp h)), if_neg hf]

end Aux_ProphetMatchingEFGT_eq_8

open Aux_ProphetMatchingEFGT_eq_8 in
open ProphetMatchingEFGT in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x) (es : List (Edge G)) (hnd : es.Nodup)
    (e : Edge G) (he : e ∉ es) (hwd : WellDefinedOn c x (es ++ [e])) :
    prob (actProbs c x (es ++ [e])) (fun l => e ∈ greedy l)
        = unmatchedAt c x es e * (c / unmatchedAt c x es e) * x e ∧
      unmatchedAt c x es e * (c / unmatchedAt c x es e) = c := by
  obtain ⟨U, hUdef⟩ : ∃ U, U = unmatchedAt c x es e := ⟨_, rfl⟩
  have hlen : es.length < (es ++ [e]).length := by simp
  have hcU : c ≤ U := by
    have hk := hwd ⟨es.length, hlen⟩
    calc c ≤ _ := hk
      _ = U := by
        rw [hUdef]
        congr 1
        all_goals first
          | exact List.take_left
          | exact List.getElem_concat_length rfl hlen
          | simp
  have hsplit : actProbs c x (es ++ [e]) = actProbs c x es ++ [(e, c / U * x e)] := by
    rw [hUdef]
    unfold unmatchedAt actProbs
    rw [List.foldl_append]
    rfl
  have hmap : (actProbs c x es).map Prod.fst = es :=
    (map_fst_foldl c x es []).trans (by simp)
  have hUp : prob (actProbs c x es) (fun l => endsFree (greedy l) e) = U := by
    rw [hUdef]
    rfl
  have hprob : prob (actProbs c x (es ++ [e])) (fun l => e ∈ greedy l) = c / U * x e * U := by
    rw [hsplit, key (actProbs c x es) e (c / U * x e) (by rw [hmap]; exact he), hUp]
  have hU0 : U * (c / U) = c := by
    rcases eq_or_lt_of_le hc with h0 | hpos
    · rw [← h0]
      simp
    · have hne : U ≠ 0 := (lt_of_lt_of_le hpos hcU).ne'
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hne, mul_one]
  rw [← hUdef]
  refine ⟨?_, hU0⟩
  rw [hprob]
  ring
