-- Prove2me | solution 1 for PigeonholeDesign.MultiDim.assign_balanced
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:17:11.63192+00:00
-- url     : https://prove2.me/submissions/792bb657-1f24-4290-b66c-945f847a1cb2

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting
import Definitions.Def_PigeonholeDesign_Lower_Setting
set_option autoImplicit false
open PigeonholeDesign.Upper

lemma phu_card_filter_eq_count (T : ℕ) (g : Fin T → Bool) (b : Bool) :
    (Finset.univ.filter (fun t => g t = b)).card = (List.ofFn g).count b := by
  induction T with
  | zero => simp
  | succ n ih =>
    have := ih (fun i => g i.succ)
    rw [Finset.card_filter] at this ⊢
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.count_cons, ← this]
    rw [add_comm]
    simp only [beq_iff_eq]

lemma phu_prefix_inv {ι : Type*} [DecidableEq ι] (T : ℕ) (hT : Even T) (cell : ℕ → ι)
    (coin : ℕ → Bool) : ∀ n, n ≤ T → (prefixAssign T cell coin n).length = n ∧
      (prefixAssign T cell coin n).count false ≤ T / 2 ∧
      (prefixAssign T cell coin n).count true ≤ T / 2 := by
  intro n
  induction n with
  | zero => intro _; simp [prefixAssign]
  | succ n ih =>
    intro hn
    obtain ⟨hlen, h0, h1⟩ := ih (by omega)
    have hsum := List.count_false_add_count_true (prefixAssign T cell coin n)
    obtain ⟨m, hm⟩ := hT
    simp only [prefixAssign]
    generalize prefixAssign T cell coin n = L at *
    cases hc : coin n <;> split_ifs <;> simp [List.count_append, hc] <;> omega

theorem base {E ι : Type*} [DecidableEq ι] {T : ℕ} (hT : Even T)
    (hole : E → ι) (x : Fin T → E) (coin : Fin T → Bool) :
    (Finset.univ.filter (fun t => assign hole x coin t = false)).card = T / 2 ∧
    (Finset.univ.filter (fun t => assign hole x coin t = true)).card = T / 2 := by
  obtain ⟨hlen, h0, h1⟩ := phu_prefix_inv T hT (cellOf hole x) (coinOf coin) T le_rfl
  have hsum := List.count_false_add_count_true (prefixAssign T (cellOf hole x) (coinOf coin) T)
  obtain ⟨m, hm⟩ := hT
  have key : ∀ b : Bool, (Finset.univ.filter (fun t => assign hole x coin t = b)).card =
      (prefixAssign T (cellOf hole x) (coinOf coin) T).count b := by
    intro b
    rw [phu_card_filter_eq_count T _ b]
    congr 2
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp [assign]
      rw [List.getElem?_eq_getElem h2, Option.getD_some]
  rw [key, key]
  omega

theorem solution {E ι : Type*} [DecidableEq ι] (T : ℕ) (hT : Even T)
    (hole : E → ι) (x : Fin T → E) (coin : Fin T → Bool) :
    (Finset.univ.filter (fun t => PigeonholeDesign.Lower.assign hole x coin t = false)).card = T / 2 ∧
    (Finset.univ.filter (fun t => PigeonholeDesign.Lower.assign hole x coin t = true)).card = T / 2 :=
  base hT hole x coin
