-- Prove2me | solution 1 for RepellingPairs.config_eq_of_dist_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:17:39.847402+00:00
-- url     : https://prove2.me/submissions/95d0933c-02e5-4a37-a3de-cabe81ecbb3b

import Mathlib
import Definitions.Def_RepellingPairs_Config

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.ConfigEq

open RepellingPairs RepellingPairs.Config

variable {n : ℕ}

theorem onSide_dec (i j x : Fin n) :
    onSide i j x = decide ((i.val ≤ j.val ∧ i.val < x.val ∧ x.val ≤ j.val) ∨
      (j.val < i.val ∧ (i.val < x.val ∨ x.val ≤ j.val))) := by
  unfold onSide
  split_ifs with h <;> simp only [decide_eq_decide, Fin.le_def, Fin.lt_def] at h ⊢ <;> omega

/-- the point before `a`, cyclically -/
def pred' (a : Fin n) : Fin n := ⟨if a.val = 0 then n - 1 else a.val - 1, by
  have := a.2; split_ifs <;> omega⟩

/-- `b - 1` as an element of `Fin n` -/
def pm (b : Fin n) : Fin n := ⟨b.val - 1, by have := b.2; omega⟩

/-- crossing a set given by a Boolean function -/
def cr (S : Fin n → Bool) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun a b => if S a = S b then 0 else 1, fun _ _ => by simp [eq_comm]⟩

theorem chordCross_eq (i j : Fin n) (s : Sym2 (Fin n)) : chordCross i j s = cr (onSide i j) s := by
  induction s using Sym2.ind with
  | _ x y => rfl

theorem cr_id (a b : Fin n) (hab : a ≠ b) (S1 S2 : Fin n → Bool)
    (h : ∀ x, (x = a ∧ S1 x = true ∧ S2 x = false) ∨ (x = b ∧ S1 x = false ∧ S2 x = true) ∨
      (x ≠ a ∧ x ≠ b ∧ S1 x = S2 x)) (s : Sym2 (Fin n)) :
    cr S1 s + cr S2 s = cr (fun x => S1 x || S2 x) s + cr (fun x => S1 x && S2 x) s +
      2 * (if s = s(a, b) then 1 else 0) := by
  induction s using Sym2.ind with
  | _ x y =>
    simp only [cr, Sym2.lift_mk, Sym2.eq_iff]
    rcases h x with ⟨hx, h1, h2⟩ | ⟨hx, h1, h2⟩ | ⟨hx, hx', h2⟩ <;>
    rcases h y with ⟨hy, g1, g2⟩ | ⟨hy, g1, g2⟩ | ⟨hy, hy', g2⟩ <;>
    all_goals (simp_all [hab, (Ne.symm hab)])
    all_goals (split_ifs <;> simp_all [hab, (Ne.symm hab)])

theorem point_cases (a b : Fin n) (hab : a < b) (x : Fin n) :
    (x = a ∧ onSide (pred' a) (pm b) x = true ∧ onSide a b x = false) ∨
    (x = b ∧ onSide (pred' a) (pm b) x = false ∧ onSide a b x = true) ∨
    (x ≠ a ∧ x ≠ b ∧ onSide (pred' a) (pm b) x = onSide a b x) := by
  have hab' : a.val < b.val := hab
  have hx := x.2
  have hb := b.2
  simp only [onSide_dec, decide_eq_decide, decide_eq_true_eq, decide_eq_false_iff_not, pred', pm]
  by_cases hxa : x.val = a.val
  · left
    refine ⟨Fin.ext hxa, ?_⟩
    split_ifs <;> omega
  · by_cases hxb : x.val = b.val
    · right; left
      refine ⟨Fin.ext hxb, ?_⟩
      split_ifs <;> omega
    · right; right
      refine ⟨fun h => hxa (by rw [h]), fun h => hxb (by rw [h]), ?_⟩
      split_ifs <;> omega

theorem inter_eq (a b x : Fin n) (hab : a < b) :
    (onSide (pred' a) (pm b) x && onSide a b x) = onSide a (pm b) x := by
  have hab' : a.val < b.val := hab
  have hx := x.2
  have hb := b.2
  simp only [onSide_dec, pred', pm, ← Bool.decide_and, decide_eq_decide]
  split_ifs <;> omega

theorem union_cases (a b : Fin n) (hab : a < b) :
    (∀ x, (onSide (pred' a) (pm b) x || onSide a b x) = onSide (pred' a) b x) ∨
    ((∀ x, (onSide (pred' a) (pm b) x || onSide a b x) = true) ∧
      ∀ x, onSide (pred' a) b x = false) := by
  have hab' : a.val < b.val := hab
  have hb := b.2
  by_cases h : a.val = 0 ∧ b.val = n - 1
  · right
    constructor
    · intro x
      have hx := x.2
      simp only [onSide_dec, pred', pm, ← Bool.decide_or, decide_eq_true_eq]
      split_ifs <;> omega
    · intro x
      have hx := x.2
      simp only [onSide_dec, pred', decide_eq_false_iff_not]
      split_ifs <;> omega
  · left
    intro x
    have hx := x.2
    simp only [onSide_dec, pred', pm, ← Bool.decide_or, decide_eq_decide]
    split_ifs <;> omega

theorem chord_id (a b : Fin n) (hab : a < b) (s : Sym2 (Fin n)) :
    chordCross (pred' a) (pm b) s + chordCross a b s =
      chordCross (pred' a) b s + chordCross a (pm b) s + 2 * (if s = s(a, b) then 1 else 0) := by
  have key := cr_id a b (Fin.ne_of_lt hab) (onSide (pred' a) (pm b)) (onSide a b)
    (point_cases a b hab) s
  have h4 : (fun x => onSide (pred' a) (pm b) x && onSide a b x) = onSide a (pm b) := by
    funext x; exact inter_eq a b x hab
  rw [h4] at key
  have h3 : cr (fun x => onSide (pred' a) (pm b) x || onSide a b x) s = cr (onSide (pred' a) b) s := by
    rcases union_cases a b hab with h | ⟨h, h'⟩
    · congr 1; funext x; exact h x
    · induction s using Sym2.ind with
      | _ x y => simp [cr, h, h']
  rw [h3] at key
  simp only [chordCross_eq]
  exact key

theorem cut_id (a b : Fin n) (hab : a < b) (C : Config n) :
    C.dist (pred' a) (pm b) + C.dist a b =
      C.dist (pred' a) b + C.dist a (pm b) + 2 * C.count s(a, b) := by
  induction C using Multiset.induction_on with
  | empty => simp [Config.dist]
  | cons s C ih =>
    simp only [Config.dist, Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons] at ih ⊢
    have := chord_id a b hab s
    have e : (s(a, b) = s) ↔ (s = s(a, b)) := eq_comm
    simp only [e]
    split_ifs at this ⊢ <;> omega

theorem cnt_off (C C' : Config n) (h : ∀ i j, Config.dist C i j = Config.dist C' i j)
    (a b : Fin n) (hab : a ≠ b) : C.count s(a, b) = C'.count s(a, b) := by
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have h1 := cut_id a b hlt C
    have h2 := cut_id a b hlt C'
    rw [h, h, h, h] at h1
    omega
  · have h1 := cut_id b a hlt C
    have h2 := cut_id b a hlt C'
    rw [h, h, h, h] at h1
    rw [Sym2.eq_swap]
    omega

theorem chordDeg_eq (t : Fin n) (s : Sym2 (Fin n)) :
    chordDeg t s = 2 * (if s = s(t, t) then 1 else 0) +
      ∑ b ∈ Finset.univ.erase t, (if s(t, b) = s then 1 else 0) := by
  induction s using Sym2.ind with
  | _ x y =>
    simp only [chordDeg, Sym2.lift_mk, Sym2.eq_iff]
    by_cases hx : x = t <;> by_cases hy : y = t
    · subst hx; subst hy; simp
    · subst hx
      have : (∑ b ∈ Finset.univ.erase x, (if (x = x ∧ b = y) ∨ (x = y ∧ b = x) then 1 else 0)) = 1 := by
        rw [Finset.sum_eq_single y]
        · simp
        · intro b _ hb; simp [hb, Ne.symm hy]
        · intro h; exact absurd (Finset.mem_erase.2 ⟨hy, Finset.mem_univ _⟩) h
      rw [this]; simp [hy]
    · subst hy
      have : (∑ b ∈ Finset.univ.erase y, (if (y = x ∧ b = y) ∨ (y = y ∧ b = x) then 1 else 0)) = 1 := by
        rw [Finset.sum_eq_single x]
        · simp
        · intro b _ hb; simp [hb, Ne.symm hx]
        · intro h; exact absurd (Finset.mem_erase.2 ⟨hx, Finset.mem_univ _⟩) h
      rw [this]; simp [hx]
    · have : (∑ b ∈ Finset.univ.erase t, (if (t = x ∧ b = y) ∨ (t = y ∧ b = x) then 1 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro b _
        simp [Ne.symm hx, Ne.symm hy]
      rw [this]; simp [hx, hy, Ne.symm hx]

theorem deg_eq (C : Config n) (t : Fin n) :
    Config.deg C t = 2 * C.count s(t, t) + ∑ b ∈ Finset.univ.erase t, C.count s(t, b) := by
  induction C using Multiset.induction_on with
  | empty => simp [Config.deg]
  | cons s C ih =>
    simp only [Config.deg, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
    rw [ih, chordDeg_eq]
    simp only [Multiset.count_cons, Finset.sum_add_distrib]
    have e : ∀ b : Fin n, (s(t, b) = s) ↔ (s = s(t, b)) := fun b => eq_comm
    simp only [e]
    simp only [Nat.mul_add]
    omega

end RepellingPairs.Dev.ConfigEq

namespace RepellingPairs

open RepellingPairs.Dev.ConfigEq

theorem chk_config_eq_of_dist_eq {n : ℕ} (C C' : Config n)
    (hdeg : ∀ t, Config.deg C t = Config.deg C' t)
    (h : ∀ i j, Config.dist C i j = Config.dist C' i j) : C = C' := by
  rw [Multiset.ext]
  intro s
  induction s using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      have h1 := deg_eq C x
      have h2 := deg_eq C' x
      have h3 : ∑ b ∈ Finset.univ.erase x, C.count s(x, b) =
          ∑ b ∈ Finset.univ.erase x, C'.count s(x, b) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact cnt_off C C' h x b (Ne.symm (Finset.ne_of_mem_erase hb))
      have := hdeg x
      omega
    · exact cnt_off C C' h x y hxy

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_config_eq_of_dist_eq := @RepellingPairs.chk_config_eq_of_dist_eq
