-- Prove2me | solution 1 for WordProblem.computablePred_of_hasDecidableWordProblem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-12T16:13:02.773298+00:00
-- url     : https://prove2.me/submissions/c63aabf7-d72b-4961-abc6-e9277a8458d8

import Mathlib
import Definitions.Def_BooneHigman

open OAI.FiniteAlgebraicEnvelopes

namespace WordProblem

universe u

/-- The word obtained by reversing and flipping every sign evaluates to the inverse. -/
theorem evalWord_inv {H : Type u} [Group H] {n : ℕ} (p : Fin n → H) (w : Word n) :
    evalWord p (w.reverse.map (fun l => (l.1, !l.2))) = (evalWord p w)⁻¹ := by
  induction w with
  | nil => simp [evalWord]
  | cons a rest ih =>
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    have hsplit : evalWord p (rest.reverse.map (fun l => (l.1, !l.2)) ++ [(a.1, !a.2)])
        = evalWord p (rest.reverse.map (fun l => (l.1, !l.2))) *
          evalWord p [(a.1, !a.2)] := by
      unfold evalWord
      rw [List.map_append, List.prod_append]
    rw [hsplit, ih]
    unfold evalWord
    by_cases h : a.2 <;> simp [h]

/-- Every element of `H` is `evalWord p` of some word over a tuple whose closure is `H`. -/
theorem exists_word_eq {H : Type u} [Group H] {n : ℕ} (p : Fin n → H)
    (hp : Subgroup.closure (Set.range p) = ⊤) (x : H) :
    ∃ w : Word n, evalWord p w = x := by
  have hx : x ∈ Subgroup.closure (Set.range p) := hp ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨[(i, true)], by simp [evalWord]⟩
  | one => exact ⟨[], by simp [evalWord]⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨wx, hwx⟩ := ihx
    obtain ⟨wy, hwy⟩ := ihy
    refine ⟨wx ++ wy, ?_⟩
    unfold evalWord
    rw [List.map_append, List.prod_append]
    unfold evalWord at hwx hwy
    rw [hwx, hwy]
  | inv x _ ihx =>
    obtain ⟨wx, hwx⟩ := ihx
    exact ⟨wx.reverse.map (fun l => (l.1, !l.2)), by rw [evalWord_inv, hwx]⟩

end WordProblem

universe u

open OAI.FiniteAlgebraicEnvelopes WordProblem in
theorem solution {H : Type u} [Group H]
    (hH : HasDecidableWordProblem H) {m : ℕ} (h : Fin m → H) :
    ComputablePred (fun word : Word m => evalWord h word = 1) := by
  classical
  obtain ⟨n, p, hp, hcomp⟩ := hH
  choose v hv using fun i => exists_word_eq p hp (h i)
  let substLetter : Fin m × Bool → Word n :=
    fun letter => cond letter.2 (v letter.1) ((v letter.1).reverse.map (fun l => (l.1, !l.2)))
  let subst : Word m → Word n := fun word => word.flatMap substLetter
  have hsubst : ∀ word : Word m, evalWord h word = evalWord p (subst word) := by
    intro word
    induction word with
    | nil => simp [evalWord, subst]
    | cons a rest ih =>
      show evalWord h (a :: rest) = evalWord p ((a :: rest).flatMap substLetter)
      have hleft : evalWord h (a :: rest) =
          (if a.2 then h a.1 else (h a.1)⁻¹) * evalWord h rest := by
        unfold evalWord; simp
      have hflat : (a :: rest).flatMap substLetter = substLetter a ++ rest.flatMap substLetter := by
        simp [List.flatMap_cons]
      have hright : evalWord p (substLetter a ++ rest.flatMap substLetter) =
          evalWord p (substLetter a) * evalWord p (rest.flatMap substLetter) := by
        unfold evalWord; rw [List.map_append, List.prod_append]
      rw [hleft, hflat, hright, ← ih]
      congr 1
      by_cases hsign : a.2
      · simp [substLetter, hsign, hv a.1]
      · have hL : substLetter a = (v a.1).reverse.map (fun l => (l.1, !l.2)) := by
          simp [substLetter, hsign]
        rw [hL, evalWord_inv, hv a.1]
        simp [hsign]
  have hComputableSubst : Computable subst := by
    have hv_primrec : Primrec v := Primrec.fin_app.comp (Primrec.const v) Primrec.id
    have hflip_primrec : Primrec (fun l : Fin n × Bool => (l.1, !l.2)) :=
      Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
    have hvrev_primrec : Primrec (fun i : Fin m => (v i).reverse) :=
      Primrec.list_reverse.comp hv_primrec
    have hfinv_primrec : Primrec (fun i : Fin m => (v i).reverse.map (fun l => (l.1, !l.2))) :=
      Primrec.list_map hvrev_primrec (hflip_primrec.comp Primrec.snd)
    have hsubstLetter_primrec : Primrec substLetter :=
      Primrec.cond Primrec.snd (hv_primrec.comp Primrec.fst) (hfinv_primrec.comp Primrec.fst)
    have hsubst_primrec : Primrec subst :=
      Primrec.list_flatMap Primrec.id (hsubstLetter_primrec.comp Primrec.snd)
    exact hsubst_primrec.to_comp
  obtain ⟨hdec, hd⟩ := hcomp
  have hComp2 : ComputablePred (fun word : Word m => evalWord p (subst word) = 1) :=
    ⟨fun word => hdec (subst word), hd.comp hComputableSubst⟩
  exact hComp2.of_eq (fun word => by rw [hsubst])
