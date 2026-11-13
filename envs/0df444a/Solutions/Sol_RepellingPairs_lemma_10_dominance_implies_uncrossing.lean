-- Prove2me | solution 1 for RepellingPairs.lemma_10_dominance_implies_uncrossing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:42:53.529204+00:00
-- url     : https://prove2.me/submissions/c47bc4f2-8fc9-4253-acbf-762b6e8d7a82

import Mathlib
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Theorems.Thm_RepellingPairs_lemma_11_uncrossing_step

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.L10Eq

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

end RepellingPairs.Dev.L10Eq

namespace RepellingPairs.Dev.L10Eq

theorem config_eq {n : ℕ} (C C' : Config n)
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

end RepellingPairs.Dev.L10Eq
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace RepellingPairs.Dev.Lemma10Proj

open RepellingPairs RepellingPairs.Config

variable {a b : ℕ}

abbrev Mv (C D : Config b) : Prop := UncrossStep C D ∨ DegenerateStep C D

abbrev RR (C D : Config b) : Prop := Relation.ReflTransGen Mv C D

theorem rr_of_mv {C D : Config b} (h : Mv C D) : RR C D := Relation.ReflTransGen.single h

theorem dg (x y w : Fin b) (rest : Config b) (hxy : x ≠ y) (hxw : x ≠ w) :
    RR (s(x, y) ::ₘ s(x, w) ::ₘ rest) (s(x, x) ::ₘ s(y, w) ::ₘ rest) :=
  rr_of_mv (Or.inr ⟨x, y, w, rest, hxy, hxw, rfl, rfl⟩)

theorem rr_congr {S S' T T' : Config b} (hS : S = S') (hT : T = T') (h : RR S' T') : RR S T := by
  subst hS; subst hT; exact h

theorem rr_eq {S T : Config b} (h : S = T) : RR S T := h ▸ Relation.ReflTransGen.refl

theorem key4 (q1 q2 q3 q4 : Fin b) (h12 : q1 ≤ q2) (h23 : q2 ≤ q3) (h34 : q3 ≤ q4)
    (rest : Config b) :
    RR (s(q1, q3) ::ₘ s(q2, q4) ::ₘ rest) (s(q1, q2) ::ₘ s(q3, q4) ::ₘ rest) ∧
    RR (s(q1, q3) ::ₘ s(q2, q4) ::ₘ rest) (s(q1, q4) ::ₘ s(q2, q3) ::ₘ rest) := by
  rcases h12.lt_or_eq with h1 | h1 <;> rcases h23.lt_or_eq with h2 | h2 <;>
    rcases h34.lt_or_eq with h3 | h3
  · -- all strict
    have hc : ChordsCross q1 q3 q2 q4 := Or.inl (Or.inl ⟨h1, h2, h3⟩)
    refine ⟨rr_of_mv (Or.inl ⟨q1, q3, q2, q4, rest, hc, rfl, Or.inl rfl⟩),
      rr_of_mv (Or.inl ⟨q1, q3, q2, q4, rest, hc, rfl, Or.inr ?_⟩)⟩
    simp [Sym2.eq_swap]
  · -- q1 < q2 < q3 = q4
    subst h3
    exact ⟨rr_congr (by simp [Sym2.eq_swap]) (by simp [Sym2.eq_swap, Multiset.cons_swap])
      (dg q3 q1 q2 rest (ne_of_gt (lt_trans h1 h2)) (ne_of_gt h2)), rr_eq rfl⟩
  · -- q1 < q2 = q3 < q4
    subst h2
    exact ⟨rr_eq rfl, rr_congr (by simp [Sym2.eq_swap]) (by simp [Sym2.eq_swap, Multiset.cons_swap])
      (dg q2 q1 q4 rest (ne_of_gt h1) (ne_of_lt h3))⟩
  · -- q1 < q2 = q3 = q4
    subst h2; subst h3
    exact ⟨rr_eq rfl, rr_eq rfl⟩
  · -- q1 = q2 < q3 < q4
    subst h1
    exact ⟨rr_congr rfl (by simp [Sym2.eq_swap, Multiset.cons_swap])
      (dg q1 q3 q4 rest (ne_of_lt h2) (ne_of_lt (lt_trans h2 h3))), rr_eq (by simp [Sym2.eq_swap, Multiset.cons_swap])⟩
  · -- q1 = q2 < q3 = q4
    subst h1; subst h3
    exact ⟨rr_congr rfl rfl (dg q1 q3 q3 rest (ne_of_lt h2) (ne_of_lt h2)), rr_eq rfl⟩
  · -- q1 = q2 = q3 < q4
    subst h1; subst h2
    exact ⟨rr_eq rfl, rr_eq (by simp [Sym2.eq_swap, Multiset.cons_swap])⟩
  · subst h1; subst h2; subst h3
    exact ⟨rr_eq rfl, rr_eq rfl⟩


theorem norm4 (x y z w : Fin a) (hc : ChordsCross x y z w) (rest : Config a) :
    ∃ p1 p2 p3 p4 : Fin a, p1 < p2 ∧ p2 < p3 ∧ p3 < p4 ∧
      s(x, y) ::ₘ s(z, w) ::ₘ rest = s(p1, p3) ::ₘ s(p2, p4) ::ₘ rest ∧
      ((s(x, z) ::ₘ s(y, w) ::ₘ rest = s(p1, p2) ::ₘ s(p3, p4) ::ₘ rest) ∨
        (s(x, z) ::ₘ s(y, w) ::ₘ rest = s(p1, p4) ::ₘ s(p2, p3) ::ₘ rest)) ∧
      ((s(x, w) ::ₘ s(y, z) ::ₘ rest = s(p1, p2) ::ₘ s(p3, p4) ::ₘ rest) ∨
        (s(x, w) ::ₘ s(y, z) ::ₘ rest = s(p1, p4) ::ₘ s(p2, p3) ::ₘ rest)) := by
  unfold ChordsCross CyclicallyOrdered at hc
  rcases hc with (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) |
      (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · refine ⟨x, z, y, w, h1, h2, h3, ?_, ?_, ?_⟩ <;>
      first
      | (simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (left; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (right; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
  · refine ⟨z, y, w, x, h1, h2, h3, ?_, ?_, ?_⟩ <;>
      first
      | (simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (left; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (right; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
  · refine ⟨y, w, x, z, h1, h2, h3, ?_, ?_, ?_⟩ <;>
      first
      | (simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (left; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (right; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
  · refine ⟨w, x, z, y, h1, h2, h3, ?_, ?_, ?_⟩ <;>
      first
      | (simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (left; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (right; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
  · refine ⟨x, w, y, z, h1, h2, h3, ?_, ?_, ?_⟩ <;>
      first
      | (simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (left; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (right; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
  · refine ⟨w, y, z, x, h1, h2, h3, ?_, ?_, ?_⟩ <;>
      first
      | (simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (left; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (right; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
  · refine ⟨y, z, x, w, h1, h2, h3, ?_, ?_, ?_⟩ <;>
      first
      | (simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (left; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (right; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
  · refine ⟨z, x, w, y, h1, h2, h3, ?_, ?_, ?_⟩ <;>
      first
      | (simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (left; simp [Sym2.eq_swap, Multiset.cons_swap]; done)
      | (right; simp [Sym2.eq_swap, Multiset.cons_swap]; done)


/-- The image of a configuration under a map of the points. -/
def img (f : Fin a → Fin b) (C : Config a) : Config b := C.map (Sym2.map f)

theorem img_cons (f : Fin a → Fin b) (x y : Fin a) (C : Config a) :
    img f (s(x, y) ::ₘ C) = s(f x, f y) ::ₘ img f C := by
  simp [img]

theorem step_map (f : Fin a → Fin b) (hf : Monotone f) {C D : Config a} (h : Mv C D) :
    RR (img f C) (img f D) := by
  rcases h with ⟨x, y, z, w, rest, hc, rfl, hD⟩ | ⟨x, y, w, rest, hxy, hxw, rfl, rfl⟩
  · obtain ⟨p1, p2, p3, p4, h1, h2, h3, e0, eA, eB⟩ := norm4 x y z w hc rest
    have k := key4 (f p1) (f p2) (f p3) (f p4) (hf h1.le) (hf h2.le) (hf h3.le) (img f rest)
    rw [e0]
    rcases hD with rfl | rfl
    · rcases eA with e | e <;> rw [e]
      · simpa only [img_cons] using k.1
      · simpa only [img_cons] using k.2
    · rcases eB with e | e <;> rw [e]
      · simpa only [img_cons] using k.1
      · simpa only [img_cons] using k.2
  · simp only [img_cons]
    by_cases h1 : f x = f y
    · apply rr_eq
      rw [← h1] <;> simp [Sym2.eq_swap, Multiset.cons_swap]
    · by_cases h2 : f x = f w
      · apply rr_eq
        rw [← h2] <;> simp [Sym2.eq_swap, Multiset.cons_swap]
      · exact dg _ _ _ _ h1 h2

/-- Monotone images of a path of moves are paths of moves. -/
theorem reaches_map (f : Fin a → Fin b) (hf : Monotone f) {C D : Config a}
    (h : Config.Reaches C D) : Config.Reaches (img f C) (img f D) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.trans (step_map f hf hs)

end RepellingPairs.Dev.Lemma10Proj
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Lemma10PM

open RepellingPairs RepellingPairs.Config

variable {n : ℕ}

/-! ### A potential that uncrossing decreases -/

def psi (n : ℕ) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun a b => Nat.dist a.val b.val * (n - Nat.dist a.val b.val),
    fun a b => by dsimp only; rw [Nat.dist_comm]⟩

def Phi (C : Config n) : ℕ := (C.map (psi n)).sum

theorem Phi_cons (s : Sym2 (Fin n)) (C : Config n) : Phi (s ::ₘ C) = psi n s + Phi C := by
  simp [Phi]

theorem psi_mk (a b : Fin n) : psi n s(a, b) = Nat.dist a.val b.val * (n - Nat.dist a.val b.val) := rfl

theorem arith (n a b c d : ℕ) (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < n) :
    ((b - a) * (n - (b - a)) + (d - c) * (n - (d - c)) < (c - a) * (n - (c - a)) + (d - b) * (n - (d - b))) ∧
    ((d - a) * (n - (d - a)) + (c - b) * (n - (c - b)) < (c - a) * (n - (c - a)) + (d - b) * (n - (d - b))) := by
  obtain ⟨x, rfl⟩ : ∃ x, b = a + x + 1 := ⟨b - a - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, c = a + x + 1 + y + 1 := ⟨c - (a + x + 1) - 1, by omega⟩
  obtain ⟨z, rfl⟩ : ∃ z, d = a + x + 1 + y + 1 + z + 1 := ⟨d - (a + x + 1 + y + 1) - 1, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w, n = a + x + 1 + y + 1 + z + 1 + w + 1 := ⟨n - (a + x + 1 + y + 1 + z + 1) - 1, by omega⟩
  have e1 : a + x + 1 - a = x + 1 := by omega
  have e2 : a + x + 1 + y + 1 + z + 1 - (a + x + 1 + y + 1) = z + 1 := by omega
  have e3 : a + x + 1 + y + 1 - a = x + y + 2 := by omega
  have e4 : a + x + 1 + y + 1 + z + 1 - (a + x + 1) = y + z + 2 := by omega
  have e5 : a + x + 1 + y + 1 + z + 1 - a = x + y + z + 3 := by omega
  have e6 : a + x + 1 + y + 1 - (a + x + 1) = y + 1 := by omega
  rw [e1, e2, e3, e4, e5, e6]
  have f1 : a + x + 1 + y + 1 + z + 1 + w + 1 - (x + 1) = a + y + z + w + 3 := by omega
  have f2 : a + x + 1 + y + 1 + z + 1 + w + 1 - (z + 1) = a + x + y + w + 3 := by omega
  have f3 : a + x + 1 + y + 1 + z + 1 + w + 1 - (x + y + 2) = a + z + w + 2 := by omega
  have f4 : a + x + 1 + y + 1 + z + 1 + w + 1 - (y + z + 2) = a + x + w + 2 := by omega
  have f5 : a + x + 1 + y + 1 + z + 1 + w + 1 - (x + y + z + 3) = a + w + 1 := by omega
  have f6 : a + x + 1 + y + 1 + z + 1 + w + 1 - (y + 1) = a + x + z + w + 3 := by omega
  rw [f1, f2, f3, f4, f5, f6]
  constructor
  · have : (x + y + 2) * (a + z + w + 2) + (y + z + 2) * (a + x + w + 2) =
        (x + 1) * (a + y + z + w + 3) + (z + 1) * (a + x + y + w + 3) + 2 * ((y + 1) * (a + w + 1)) := by
      ring
    have hp : 0 < (y + 1) * (a + w + 1) := by positivity
    omega
  · have : (x + y + 2) * (a + z + w + 2) + (y + z + 2) * (a + x + w + 2) =
        (x + y + z + 3) * (a + w + 1) + (y + 1) * (a + x + z + w + 3) + 2 * ((x + 1) * (z + 1)) := by
      ring
    have hp : 0 < (x + 1) * (z + 1) := by positivity
    omega

theorem psi_lt (a b : Fin n) (h : a < b) :
    psi n s(a, b) = (b.val - a.val) * (n - (b.val - a.val)) := by
  rw [psi_mk, Nat.dist_eq_sub_of_le (le_of_lt h)]

theorem Phi_step {C D : Config n} (h : UncrossStep C D) : Phi D < Phi C := by
  obtain ⟨x, y, z, w, rest, hc, rfl, hD⟩ := h
  obtain ⟨p1, p2, p3, p4, h1, h2, h3, e0, eA, eB⟩ := RepellingPairs.Dev.Lemma10Proj.norm4 x y z w hc rest
  have hn := p4.2
  have ar := arith n p1.val p2.val p3.val p4.val h1 h2 h3 hn
  have s13 := psi_lt p1 p3 (lt_trans h1 h2)
  have s24 := psi_lt p2 p4 (lt_trans h2 h3)
  have s12 := psi_lt p1 p2 h1
  have s34 := psi_lt p3 p4 h3
  have s14 := psi_lt p1 p4 (lt_trans (lt_trans h1 h2) h3)
  have s23 := psi_lt p2 p3 h2
  have hS : Phi (s(x, y) ::ₘ s(z, w) ::ₘ rest) = psi n s(p1, p3) + psi n s(p2, p4) + Phi rest := by
    rw [e0, Phi_cons, Phi_cons]; ring
  rw [hS, s13, s24]
  have eT : ∀ q r q' r' : Sym2 (Fin n), q ::ₘ r ::ₘ rest = q' ::ₘ r' ::ₘ rest →
      Phi (q ::ₘ r ::ₘ rest) = psi n q' + psi n r' + Phi rest := by
    intro q r q' r' e; rw [e, Phi_cons, Phi_cons]; ring
  rcases hD with rfl | rfl
  · rcases eA with e | e
    · rw [eT _ _ _ _ e, s12, s34]; omega
    · rw [eT _ _ _ _ e, s14, s23]; omega
  · rcases eB with e | e
    · rw [eT _ _ _ _ e, s12, s34]; omega
    · rw [eT _ _ _ _ e, s14, s23]; omega

theorem chordDeg_mk (t a b : Fin n) :
    chordDeg t s(a, b) = (if a = t then 1 else 0) + (if b = t then 1 else 0) := rfl

theorem deg_cons (t : Fin n) (s : Sym2 (Fin n)) (C : Config n) :
    deg (s ::ₘ C) t = chordDeg t s + deg C t := by
  simp [deg]

theorem deg_step {C D : Config n} (h : UncrossStep C D) (t : Fin n) : deg D t = deg C t := by
  obtain ⟨x, y, z, w, rest, hc, rfl, hD⟩ := h
  rcases hD with rfl | rfl <;>
  · simp only [deg_cons, chordDeg_mk]; omega

/-! ### Configurations of degree one are perfect matchings -/

theorem chordDeg_pos {t : Fin n} {s : Sym2 (Fin n)} (h : t ∈ s) : 1 ≤ chordDeg t s := by
  induction s using Sym2.ind with
  | _ a b =>
    rw [Sym2.mem_iff] at h
    rw [chordDeg_mk]
    rcases h with rfl | rfl <;> simp

theorem mem_of_chordDeg {t : Fin n} {s : Sym2 (Fin n)} (h : 1 ≤ chordDeg t s) : t ∈ s := by
  induction s using Sym2.ind with
  | _ a b =>
    rw [chordDeg_mk] at h
    rw [Sym2.mem_iff]
    by_cases ha : a = t
    · exact Or.inl ha.symm
    · by_cases hb : b = t
      · exact Or.inr hb.symm
      · simp [ha, hb] at h

theorem chordDeg_le_deg {t : Fin n} {C : Config n} {s : Sym2 (Fin n)} (hs : s ∈ C) :
    chordDeg t s ≤ deg C t := by
  unfold deg
  exact Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ (Multiset.mem_map_of_mem _ hs)

theorem exists_pm (C : Config n) (h1 : ∀ t, deg C t = 1) :
    ∃ P : PerfectMatching n, P.config = C := by
  have hex : ∀ t, ∃ s ∈ C, t ∈ s := by
    intro t
    by_contra hcon
    push Not at hcon
    have : deg C t = 0 := by
      unfold deg
      apply Multiset.sum_eq_zero
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
      by_contra hne
      exact hcon s hs (mem_of_chordDeg (by omega))
    have := h1 t
    omega
  have hnl : ∀ s ∈ C, ¬ s.IsDiag := by
    intro s hs hd
    induction s using Sym2.ind with
    | _ a b =>
      have hab : a = b := by simpa using hd
      subst hab
      have := chordDeg_le_deg (t := a) hs
      rw [chordDeg_mk] at this
      have := h1 a
      simp_all
  have huniq : ∀ t (s s' : Sym2 (Fin n)), s ∈ C → s' ∈ C → t ∈ s → t ∈ s' → s = s' := by
    intro t s s' hs hs' hts hts'
    obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem hs
    have hd := h1 t
    rw [deg_cons] at hd
    have hp := chordDeg_pos hts
    have hR : deg R t = 0 := by omega
    rcases Multiset.mem_cons.1 hs' with h | h
    · exact h.symm
    · have := chordDeg_le_deg (t := t) h
      have := chordDeg_pos hts'
      omega
  choose ch hchC hcht using hex
  have hch : ∀ t s, s ∈ C → t ∈ s → s = ch t := fun t s hs ht => huniq t s (ch t) hs (hchC t) ht (hcht t)
  let partner : Fin n → Fin n := fun t => Sym2.Mem.other (hcht t)
  have hspec : ∀ t, s(t, partner t) = ch t := fun t => Sym2.other_spec (hcht t)
  have hne : ∀ t, partner t ≠ t := by
    intro t h
    apply hnl _ (hchC t)
    rw [← hspec t, h]
    simp
  have hinv : ∀ t, partner (partner t) = t := by
    intro t
    have e1 : ch (partner t) = ch t := (hch (partner t) (ch t) (hchC t)
      (by rw [← hspec t]; simp)).symm
    have e2 := hspec (partner t)
    rw [e1, ← hspec t, Sym2.eq_iff] at e2
    rcases e2 with ⟨h, _⟩ | ⟨_, h⟩
    · exact (hne t h).elim
    · exact h
  have hnd : C.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro a
    by_contra hlt
    push Not at hlt
    have ha : a ∈ C := Multiset.count_pos.1 (by omega)
    obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem ha
    have haR : a ∈ R := by
      apply Multiset.count_pos.1
      rw [Multiset.count_cons_self] at hlt
      omega
    obtain ⟨R', rfl⟩ := Multiset.exists_cons_of_mem haR
    have hnl' := hnl a ha
    induction a using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := by simpa using hnl'
      have := h1 x
      rw [deg_cons, deg_cons, chordDeg_mk] at this
      have hyx : ¬ y = x := fun h => hxy h.symm
      simp [hyx] at this
  refine ⟨⟨partner, hinv, hne⟩, ?_⟩
  unfold PerfectMatching.config
  symm
  refine (Multiset.Nodup.ext hnd (Finset.nodup _)).2 ?_
  intro q
  rw [Finset.mem_val, Finset.mem_image]
  constructor
  · intro hq
    induction q using Sym2.ind with
    | _ x y =>
      refine ⟨x, Finset.mem_univ _, ?_⟩
      rw [hspec]
      exact (hch x _ hq (Sym2.mem_mk_left x y)).symm
  · rintro ⟨x, _, rfl⟩
    rw [hspec]
    exact hchC x

/-- Perfect matchings: `C ⪰ C'` implies `C → C'`, by the sibling Lemma 11 and induction on `Phi`. -/
theorem pm_reaches (C C' : Config n) (h1 : ∀ t, deg C t = 1)
    (hdeg : ∀ t, deg C t = deg C' t) (hd : Dominates C C') : Reaches C C' := by
  induction hΦ : Phi C using Nat.strong_induction_on generalizing C with
  | _ m ih =>
    by_cases heq : ∀ i j, dist C i j = dist C' i j
    · rw [RepellingPairs.Dev.L10Eq.config_eq C C' hdeg heq]
      exact Relation.ReflTransGen.refl
    · push Not at heq
      obtain ⟨i, j, hij⟩ := heq
      have hlt : dist C' i j < dist C i j := lt_of_le_of_ne (hd i j) (Ne.symm hij)
      have h1' : ∀ t, deg C' t = 1 := fun t => (hdeg t) ▸ h1 t
      obtain ⟨P, hP⟩ := exists_pm C h1
      obtain ⟨P', hP'⟩ := exists_pm C' h1'
      have hs : StrictlyDominates P.config P'.config := by
        rw [hP, hP']; exact ⟨hd, i, j, hlt⟩
      obtain ⟨C₁, hu, hd₁⟩ := RepellingPairs.lemma_11_uncrossing_step P P' hs
      rw [hP] at hu
      rw [hP'] at hd₁
      have hΦ1 : Phi C₁ < m := hΦ ▸ Phi_step hu
      have := ih _ hΦ1 C₁ (fun t => (deg_step hu t).trans (h1 t))
        (fun t => (deg_step hu t).trans (hdeg t)) hd₁ rfl
      exact Relation.ReflTransGen.head (Or.inl hu) this

end RepellingPairs.Dev.Lemma10PM
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Lemma10Del

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.Lemma10Proj RepellingPairs.Dev.Lemma10PM

variable {a b : ℕ}

theorem onSide_map (f : Fin a → Fin b) (hf : StrictMono f) (i j x : Fin a) :
    onSide (f i) (f j) (f x) = onSide i j x := by
  simp only [onSide, hf.le_iff_le, hf.lt_iff_lt]

theorem chordCross_map (f : Fin a → Fin b) (hf : StrictMono f) (i j : Fin a) (s : Sym2 (Fin a)) :
    chordCross (f i) (f j) (Sym2.map f s) = chordCross i j s := by
  induction s using Sym2.ind with
  | _ x y => simp [chordCross, onSide_map f hf]

theorem dist_img (f : Fin a → Fin b) (hf : StrictMono f) (C : Config a) (i j : Fin a) :
    Config.dist (img f C) (f i) (f j) = Config.dist C i j := by
  unfold Config.dist img
  rw [Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro s _
  exact chordCross_map f hf i j s

theorem chordDeg_map (f : Fin a → Fin b) (hf : Function.Injective f) (t : Fin a) (s : Sym2 (Fin a)) :
    chordDeg (f t) (Sym2.map f s) = chordDeg t s := by
  induction s using Sym2.ind with
  | _ x y => simp [chordDeg_mk, hf.eq_iff]

theorem deg_img (f : Fin a → Fin b) (hf : Function.Injective f) (C : Config a) (t : Fin a) :
    deg (img f C) (f t) = deg C t := by
  unfold deg img
  rw [Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro s _
  exact chordDeg_map f hf t s

theorem exists_pre {m : ℕ} (p : Fin (m + 1)) (C : Config (m + 1)) (hp : deg C p = 0) :
    ∃ C₀ : Config m, C = img p.succAbove C₀ := by
  have hnot : ∀ s ∈ C, p ∉ s := by
    intro s hs hps
    have := chordDeg_le_deg (t := p) hs
    have := chordDeg_pos hps
    omega
  induction C using Multiset.induction_on with
  | empty => exact ⟨0, by simp [img]⟩
  | cons s C ih =>
    have hC : deg C p = 0 := by rw [deg_cons] at hp; omega
    obtain ⟨C₀, hC₀⟩ := ih hC (fun s' hs' => hnot s' (Multiset.mem_cons_of_mem hs'))
    have hps := hnot s (Multiset.mem_cons_self s C)
    induction s using Sym2.ind with
    | _ x y =>
      rw [Sym2.mem_iff] at hps
      push Not at hps
      obtain ⟨x', hx'⟩ := Fin.exists_succAbove_eq (Ne.symm hps.1)
      obtain ⟨y', hy'⟩ := Fin.exists_succAbove_eq (Ne.symm hps.2)
      exact ⟨s(x', y') ::ₘ C₀, by rw [img_cons, hx', hy', ← hC₀]⟩

/-- D: deleting a point of degree zero. -/
theorem delete_step {m : ℕ} (C C' : Config (m + 1)) (p : Fin (m + 1)) (hp : deg C p = 0)
    (hloop : ∀ a, s(a, a) ∉ C) (hdeg : ∀ t, deg C t = deg C' t) (hd : Dominates C C') :
    ∃ C₀ C₀' : Config m, C = img p.succAbove C₀ ∧ C' = img p.succAbove C₀' ∧
      (∀ a, s(a, a) ∉ C₀) ∧ (∀ t, deg C₀ t = deg C₀' t) ∧ Dominates C₀ C₀' ∧
      ∑ t, deg C₀ t ^ 2 = ∑ t, deg C t ^ 2 := by
  have hsm := Fin.strictMono_succAbove p
  have hinj := hsm.injective
  obtain ⟨C₀, e⟩ := exists_pre p C hp
  obtain ⟨C₀', e'⟩ := exists_pre p C' (by rw [← hdeg]; exact hp)
  refine ⟨C₀, C₀', e, e', ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply hloop (p.succAbove x)
    rw [e]
    have := Multiset.mem_map_of_mem (Sym2.map p.succAbove) hx
    simpa [img] using this
  · intro t
    rw [← deg_img _ hinj, ← deg_img _ hinj, ← e, ← e', hdeg]
  · intro i j
    have := hd (p.succAbove i) (p.succAbove j)
    rw [e, e', dist_img _ hsm, dist_img _ hsm] at this
    exact this
  · rw [Fin.sum_univ_succAbove (fun t => deg C t ^ 2) p, hp]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [← deg_img _ hinj, ← e]

end RepellingPairs.Dev.Lemma10Del
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace RepellingPairs.Dev.Lemma10Split

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.Lemma10Proj RepellingPairs.Dev.Lemma10PM
  RepellingPairs.Dev.Lemma10Del

variable {n : ℕ}

/-- The embedding of `Fin n` into `Fin (n + 1)` that skips `v'`, the first copy of `v`
(`v` goes to `v''`). -/
def gS (v : Fin n) : Fin n → Fin (n + 1) := (Fin.castSucc v).succAbove

theorem gS_strictMono (v : Fin n) : StrictMono (gS v) := Fin.strictMono_succAbove _

theorem gS_ne (v : Fin n) (x : Fin n) : gS v x ≠ Fin.castSucc v := Fin.succAbove_ne _ _

theorem gS_v (v : Fin n) : gS v v = Fin.succ v := by
  simp [gS, Fin.succAbove]

theorem pi_gS (v x : Fin n) : v.predAbove (gS v x) = x := Fin.predAbove_succAbove v x

theorem pi_v1 (v : Fin n) : v.predAbove (Fin.castSucc v) = v := by
  simp [Fin.predAbove]

/-- Split the chord `c = (v, u)` of `D`: one end stays at `v'`, all other ends at `v` move to `v''`. -/
def splitCfg (v : Fin n) (D : Config n) (u : Fin n) (c : Sym2 (Fin n)) : Config (n + 1) :=
  s(Fin.castSucc v, gS v u) ::ₘ img (gS v) (D.erase c)

theorem img_pi_img (v : Fin n) (D : Config n) : img v.predAbove (img (gS v) D) = D := by
  unfold img
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id D]
  apply Multiset.map_congr rfl
  intro s _
  induction s using Sym2.ind with
  | _ x y => simp [pi_gS]

theorem split_proj (v u : Fin n) (D : Config n) (c : Sym2 (Fin n)) (hc : c ∈ D) (hcu : c = s(v, u)) :
    img v.predAbove (splitCfg v D u c) = D := by
  unfold splitCfg
  rw [img_cons, img_pi_img, pi_gS, pi_v1, ← hcu, Multiset.cons_erase hc]

theorem split_loopfree (v u : Fin n) (D : Config n) (c : Sym2 (Fin n)) (hD : ∀ a, s(a, a) ∉ D) :
    ∀ a, s(a, a) ∉ splitCfg v D u c := by
  intro a ha
  unfold splitCfg at ha
  rcases Multiset.mem_cons.1 ha with h | h
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      first
      | exact gS_ne v u (h2.symm.trans h1)
      | exact gS_ne v u (h2.symm.trans h1).symm
      | exact gS_ne v u (h1.symm.trans h2)
      | exact gS_ne v u (h1.symm.trans h2).symm
      | exact gS_ne v u (h1.trans h2.symm)
      | exact gS_ne v u (h1.trans h2.symm).symm
  · obtain ⟨s', hs', e⟩ := Multiset.mem_map.1 h
    induction s' using Sym2.ind with
    | _ x y =>
      simp only [Sym2.map_mk, Sym2.eq_iff] at e
      have hxy : x = y := by
        rcases e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact (gS_strictMono v).injective (h1.trans h2.symm)
      subst hxy
      exact hD x (Multiset.mem_of_mem_erase hs')

theorem deg_split_g (v u : Fin n) (D : Config n) (c : Sym2 (Fin n)) (hc : c ∈ D) (hcu : c = s(v, u))
    (x : Fin n) : deg (splitCfg v D u c) (gS v x) + (if x = v then 1 else 0) = deg D x := by
  have h1 : deg D x = chordDeg x c + deg (D.erase c) x := by
    conv_lhs => rw [← Multiset.cons_erase hc]
    exact deg_cons x c _
  unfold splitCfg
  rw [deg_cons, deg_img _ (gS_strictMono v).injective, h1, hcu, chordDeg_mk, chordDeg_mk]
  have : (Fin.castSucc v = gS v x) = False := by
    simp only [eq_iff_iff, iff_false]; exact fun h => gS_ne v x h.symm
  simp only [this, (gS_strictMono v).injective.eq_iff]
  by_cases h : x = v <;> by_cases h' : u = x <;> simp [h, h', eq_comm] <;> omega

theorem deg_split_v1 (v u : Fin n) (D : Config n) (c : Sym2 (Fin n)) :
    deg (splitCfg v D u c) (Fin.castSucc v) = 1 := by
  unfold splitCfg
  rw [deg_cons, chordDeg_mk]
  have h0 : deg (img (gS v) (D.erase c)) (Fin.castSucc v) = 0 := by
    unfold deg img
    apply Multiset.sum_eq_zero
    intro z hz
    obtain ⟨s', hs', rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨s'', _, rfl⟩ := Multiset.mem_map.1 hs'
    induction s'' using Sym2.ind with
    | _ x y => simp [chordDeg_mk, gS_ne v x, gS_ne v y]
  rw [h0]
  simp [gS_ne v u]

/-! ### The choice of chords -/

/-- The other end of `s` seen from `v` (`v` itself if `s` is a loop at `v`, or if `v ∉ s`). -/
noncomputable def oth (v : Fin n) (s : Sym2 (Fin n)) : Fin n := if h : v ∈ s then Sym2.Mem.other h else v

theorem oth_spec {v : Fin n} {s : Sym2 (Fin n)} (h : v ∈ s) : s = s(v, oth v s) := by
  unfold oth; rw [dif_pos h]; exact (Sym2.other_spec h).symm

/-- Clockwise distance from `v` to the other end; a loop counts as `n`. -/
noncomputable def key (v : Fin n) (s : Sym2 (Fin n)) : ℕ :=
  if oth v s = v then n else if v ≤ oth v s then (oth v s).val - v.val else (oth v s).val + n - v.val

theorem exists_at {C : Config n} (v : Fin n) (h : 1 ≤ deg C v) : ∃ s ∈ C, v ∈ s := by
  by_contra hcon
  push Not at hcon
  have : deg C v = 0 := by
    unfold deg
    apply Multiset.sum_eq_zero
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
    by_contra hne
    exact hcon s hs (mem_of_chordDeg (by omega))
  omega

theorem exists_near (C : Config n) (v : Fin n) (h : ∃ s ∈ C, v ∈ s) :
    ∃ c ∈ C, v ∈ c ∧ ∀ s ∈ C, v ∈ s → key v c ≤ key v s := by
  classical
  obtain ⟨s0, hs0, hv0⟩ := h
  have hne : (C.toFinset.filter fun s => v ∈ s).Nonempty :=
    ⟨s0, by simp [hs0, hv0]⟩
  obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image _ (key v) hne
  simp only [Finset.mem_filter, Multiset.mem_toFinset] at hc hmin
  exact ⟨c, hc.1, hc.2, fun s hs hv => hmin s ⟨hs, hv⟩⟩

theorem exists_far (C : Config n) (v : Fin n) (h : ∃ s ∈ C, v ∈ s) :
    ∃ c ∈ C, v ∈ c ∧ ∀ s ∈ C, v ∈ s → key v s ≤ key v c := by
  classical
  obtain ⟨s0, hs0, hv0⟩ := h
  have hne : (C.toFinset.filter fun s => v ∈ s).Nonempty :=
    ⟨s0, by simp [hs0, hv0]⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ (key v) hne
  simp only [Finset.mem_filter, Multiset.mem_toFinset] at hc hmax
  exact ⟨c, hc.1, hc.2, fun s hs hv => hmax s ⟨hs, hv⟩⟩

end RepellingPairs.Dev.Lemma10Split
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Lemma10Dom

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.Lemma10Proj RepellingPairs.Dev.Lemma10PM
  RepellingPairs.Dev.Lemma10Del RepellingPairs.Dev.Lemma10Split

variable {n : ℕ}

theorem gS_val (v x : Fin n) : (gS v x).val = if x.val < v.val then x.val else x.val + 1 := by
  unfold gS Fin.succAbove
  by_cases h : x.val < v.val
  · have : Fin.castSucc x < Fin.castSucc v := h
    simp [this, h]
  · have : ¬ Fin.castSucc x < Fin.castSucc v := h
    simp [this, h]

theorem dist_cons (s : Sym2 (Fin n)) (D : Config n) (i j : Fin n) :
    Config.dist (s ::ₘ D) i j = chordCross i j s + Config.dist D i j := by
  simp [Config.dist]

theorem dist_self_cut (D : Config n) (i : Fin n) : Config.dist D i i = 0 := by
  unfold Config.dist
  apply Multiset.sum_eq_zero
  intro z hz
  obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hz
  induction s using Sym2.ind with
  | _ x y =>
    have a1 : ∀ z : Fin n, (decide (i < z) && decide (z ≤ i)) = false := by
      intro z
      by_cases h : i < z
      · simp [h, not_le.2 h]
      · simp [h]
    simp [chordCross, onSide, a1]

/-- Cuts of the split circle that do not separate `v'` from `v''`. -/
theorem onSide_split (v i₀ j₀ : Fin n) :
    onSide (gS v i₀) (gS v j₀) (Fin.castSucc v) = onSide (gS v i₀) (gS v j₀) (Fin.succ v) := by
  rw [RepellingPairs.Dev.L10Eq.onSide_dec, RepellingPairs.Dev.L10Eq.onSide_dec]
  simp only [gS_val, Fin.val_castSucc, Fin.val_succ]
  simp only [decide_eq_decide]
  split_ifs <;> omega

theorem dist_split_A (v u : Fin n) (D : Config n) (c : Sym2 (Fin n)) (hc : c ∈ D) (hcu : c = s(v, u))
    (i₀ j₀ : Fin n) :
    Config.dist (splitCfg v D u c) (gS v i₀) (gS v j₀) = Config.dist D i₀ j₀ := by
  unfold splitCfg
  rw [dist_cons, dist_img _ (gS_strictMono v)]
  have h1 : Config.dist D i₀ j₀ = chordCross i₀ j₀ c + Config.dist (D.erase c) i₀ j₀ := by
    conv_lhs => rw [← Multiset.cons_erase hc]
    exact dist_cons c _ i₀ j₀
  rw [h1]
  congr 1
  rw [hcu, ← chordCross_map _ (gS_strictMono v)]
  simp only [Sym2.map_mk, gS_v]
  simp only [chordCross, Sym2.lift_mk, onSide_split]


/-! ### Cuts `(v', j)`: arcs starting at `v''` -/

/-- clockwise distance from `v` to `x` -/
def cdv (v x : Fin n) : ℕ := if v ≤ x then x.val - v.val else x.val + n - v.val

theorem cdv_zero (v x : Fin n) : cdv v x = 0 ↔ x = v := by
  have := x.2; have := v.2
  unfold cdv
  rw [Fin.ext_iff]
  simp only [Fin.le_def]
  split_ifs <;> omega

def S1f (v j₀ : Fin n) (x : Fin n) : Bool := decide (0 < cdv v x ∧ cdv v x ≤ cdv v j₀)
def S0f (v j₀ : Fin n) (x : Fin n) : Bool := decide (cdv v x ≤ cdv v j₀)

theorem S1f_eq (v j₀ x : Fin n) : S1f v j₀ x = onSide v j₀ x := by
  have := x.2; have := v.2; have := j₀.2
  rw [RepellingPairs.Dev.L10Eq.onSide_dec]
  unfold S1f cdv
  simp only [Fin.le_def, decide_eq_decide]
  split_ifs <;> omega

theorem S0f_eq (v j₀ x : Fin n) (h : j₀ ≠ RepellingPairs.Dev.L10Eq.pred' v) :
    S0f v j₀ x = onSide (RepellingPairs.Dev.L10Eq.pred' v) j₀ x := by
  have := x.2; have := v.2; have := j₀.2
  have h' : j₀.val ≠ (RepellingPairs.Dev.L10Eq.pred' v).val := fun e => h (Fin.ext e)
  rw [RepellingPairs.Dev.L10Eq.onSide_dec]
  unfold S0f cdv RepellingPairs.Dev.L10Eq.pred' at *
  simp only [Fin.le_def, decide_eq_decide] at *
  split_ifs at * <;> omega

theorem S0f_all (v j₀ x : Fin n) (h : j₀ = RepellingPairs.Dev.L10Eq.pred' v) : S0f v j₀ x = true := by
  have := x.2; have := v.2; have := j₀.2
  have h' : j₀.val = (RepellingPairs.Dev.L10Eq.pred' v).val := by rw [h]
  unfold S0f cdv RepellingPairs.Dev.L10Eq.pred' at *
  simp only [Fin.le_def, decide_eq_true_eq] at *
  split_ifs at * <;> omega

theorem S0f_v (v j₀ : Fin n) : S0f v j₀ v = true := by
  have := (cdv_zero v v).2 rfl
  simp [S0f, this]

theorem hat_v1 (v j₀ : Fin n) : onSide (Fin.castSucc v) (gS v j₀) (Fin.castSucc v) = false := by
  unfold onSide
  split_ifs with h
  · simp
  · simp; exact not_le.1 h

theorem hat_g (v j₀ x : Fin n) :
    onSide (Fin.castSucc v) (gS v j₀) (gS v x) = S0f v j₀ x := by
  have := x.2; have := v.2; have := j₀.2
  rw [RepellingPairs.Dev.L10Eq.onSide_dec]
  unfold S0f cdv
  simp only [gS_val, Fin.val_castSucc, Fin.le_def, decide_eq_decide]
  split_ifs <;> omega

/-- crossing a Boolean side -/
abbrev cr' (S : Fin n → Bool) : Sym2 (Fin n) → ℕ := RepellingPairs.Dev.L10Eq.cr S

theorem dsum (S : Fin n → Bool) (D : Config n) (i j : Fin n) (h : onSide i j = S) :
    Config.dist D i j = (D.map (cr' S)).sum := by
  unfold Config.dist
  congr 1
  apply Multiset.map_congr rfl
  intro s _
  rw [RepellingPairs.Dev.L10Eq.chordCross_eq, h]

theorem cr_map (S : Fin (n + 1) → Bool) (f : Fin n → Fin (n + 1)) (s : Sym2 (Fin n)) :
    cr' S (Sym2.map f s) = cr' (fun x => S (f x)) s := by
  induction s using Sym2.ind with
  | _ x y => rfl

/-- distance of the split configuration across the cut `(v', gS j₀)` -/
theorem dist_split_B (v u : Fin n) (D : Config n) (c : Sym2 (Fin n)) (hc : c ∈ D) (hcu : c = s(v, u))
    (j₀ : Fin n) :
    Config.dist (splitCfg v D u c) (Fin.castSucc v) (gS v j₀) + (if S0f v j₀ u then 0 else 1) =
      (if S0f v j₀ u then 1 else 0) + (D.map (cr' (S0f v j₀))).sum := by
  have hS : onSide (Fin.castSucc v) (gS v j₀) = fun a => onSide (Fin.castSucc v) (gS v j₀) a := rfl
  rw [dsum _ _ _ _ rfl]
  unfold splitCfg
  rw [Multiset.map_cons, Multiset.sum_cons, img, Multiset.map_map]
  have e1 : (D.map (cr' (S0f v j₀))).sum = cr' (S0f v j₀) c + ((D.erase c).map (cr' (S0f v j₀))).sum := by
    conv_lhs => rw [← Multiset.cons_erase hc]
    simp
  have e2 : ((D.erase c).map (cr' (S0f v j₀))).sum =
      ((D.erase c).map ((cr' (onSide (Fin.castSucc v) (gS v j₀))) ∘ Sym2.map (gS v))).sum := by
    congr 1
    apply Multiset.map_congr rfl
    intro s _
    simp only [Function.comp, cr_map, hat_g]
  have e3 : cr' (S0f v j₀) c = if S0f v j₀ u then 0 else 1 := by
    rw [hcu]
    unfold cr' RepellingPairs.Dev.L10Eq.cr
    simp [S0f_v]
  have e4 : cr' (onSide (Fin.castSucc v) (gS v j₀)) s(Fin.castSucc v, gS v u) =
      if S0f v j₀ u then 1 else 0 := by
    unfold cr' RepellingPairs.Dev.L10Eq.cr
    simp only [Sym2.lift_mk, hat_v1, hat_g]
    cases h : S0f v j₀ u <;> simp
  rw [e4, e1, e2, e3]
  omega

theorem dist_split_B' (v u : Fin n) (D : Config n) (c : Sym2 (Fin n)) (hc : c ∈ D) (hcu : c = s(v, u))
    (hu : u = v) (j₀ : Fin n) :
    Config.dist (splitCfg v D u c) (Fin.castSucc v) (gS v j₀) =
      1 + (D.map (cr' (S0f v j₀))).sum := by
  have := dist_split_B v u D c hc hcu j₀
  have h : S0f v j₀ u = true := by subst hu; exact S0f_v _ _
  rw [h] at this
  simpa using this

/-! ### Counting the chords at `v` -/

def cA (v : Fin n) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun x y => (if x = v ∧ y ≠ v then 1 else 0) + (if y = v ∧ x ≠ v then 1 else 0),
    fun _ _ => Nat.add_comm _ _⟩

def cB (v : Fin n) (S : Fin n → Bool) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun x y => (if x = v ∧ S y = true then 1 else 0) + (if y = v ∧ S x = true then 1 else 0),
    fun _ _ => Nat.add_comm _ _⟩

def cL (v : Fin n) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun x y => if x = v ∧ y = v then 1 else 0, fun x y => by simp [and_comm]⟩

theorem chordDeg_cAL (v : Fin n) (s : Sym2 (Fin n)) : chordDeg v s = cA v s + 2 * cL v s := by
  induction s using Sym2.ind with
  | _ x y =>
    simp only [chordDeg_mk, cA, cL, Sym2.lift_mk]
    by_cases hx : x = v <;> by_cases hy : y = v <;> simp [hx, hy]

theorem deg_AL (v : Fin n) (D : Config n) :
    deg D v = (D.map (cA v)).sum + 2 * (D.map (cL v)).sum := by
  unfold deg
  rw [show (D.map (chordDeg v)).sum = (D.map (fun s => cA v s + 2 * cL v s)).sum from
    congrArg _ (Multiset.map_congr rfl fun s _ => chordDeg_cAL v s)]
  rw [Multiset.sum_map_add, Multiset.sum_map_mul_left]

theorem cr_AB (v : Fin n) (S1 : Fin n → Bool) (h : S1 v = false) (s : Sym2 (Fin n)) :
    cr' S1 s + cA v s = cr' (fun x => S1 x || decide (x = v)) s + 2 * cB v S1 s := by
  induction s using Sym2.ind with
  | _ x y =>
    simp only [cr', RepellingPairs.Dev.L10Eq.cr, cA, cB, Sym2.lift_mk]
    by_cases hx : x = v <;> by_cases hy : y = v
    · subst hx; subst hy; simp [h]
    · subst hx; rcases Bool.eq_false_or_eq_true (S1 y) with h1 | h1 <;> simp [h, h1, hy]
    · subst hy; rcases Bool.eq_false_or_eq_true (S1 x) with h1 | h1 <;> simp [h, h1, hx]
    · rcases Bool.eq_false_or_eq_true (S1 x) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (S1 y) with h2 | h2 <;> simp [h1, h2, hx, hy]

theorem sum_AB (v : Fin n) (S1 : Fin n → Bool) (h : S1 v = false) (D : Config n) :
    (D.map (cr' S1)).sum + (D.map (cA v)).sum =
      (D.map (cr' (fun x => S1 x || decide (x = v)))).sum + 2 * (D.map (cB v S1)).sum := by
  rw [← Multiset.sum_map_add, ← Multiset.sum_map_mul_left, ← Multiset.sum_map_add]
  exact congrArg _ (Multiset.map_congr rfl fun s _ => cr_AB v S1 h s)

theorem oth_mk (v y : Fin n) : oth v s(v, y) = y := by
  have h := oth_spec (Sym2.mem_mk_left v y)
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, h2⟩ | ⟨h1, h2⟩
  · exact h2.symm
  · exact h1.symm.trans h2.symm

theorem key_mk (v y : Fin n) (hy : y ≠ v) : key v s(v, y) = cdv v y := by
  unfold key cdv
  rw [oth_mk, if_neg hy]

theorem split_dom_B (C C' : Config n) (v : Fin n) (c1 c1' : Sym2 (Fin n))
    (hloop : ∀ a, s(a, a) ∉ C) (hdeg : ∀ t, deg C t = deg C' t) (hd : Dominates C C')
    (hc1 : c1 ∈ C) (hvc1 : v ∈ c1) (hc1' : c1' ∈ C') (hvc1' : v ∈ c1')
    (hnear : ∀ s ∈ C, v ∈ s → key v c1 ≤ key v s)
    (hv : 2 ≤ deg C v) (j₀ : Fin n) :
    Config.dist (splitCfg v C' (oth v c1') c1') (Fin.castSucc v) (gS v j₀) ≤
      Config.dist (splitCfg v C (oth v c1) c1) (Fin.castSucc v) (gS v j₀) := by
  have e1 := oth_spec hvc1
  have e1' := oth_spec hvc1'
  set u1 := oth v c1 with hu1
  set w := oth v c1' with hw
  have hu1v : u1 ≠ v := by
    intro h
    apply hloop v
    rw [e1, h] at hc1
    exact hc1
  have SB := dist_split_B v u1 C c1 hc1 e1 j₀
  -- the sides
  have hS1v : S1f v j₀ v = false := by simp [S1f, cdv]
  have hS0 : (fun x => S1f v j₀ x || decide (x = v)) = S0f v j₀ := by
    funext x
    unfold S1f S0f
    by_cases hx : x = v
    · subst hx; simp [cdv]
    · have := (cdv_zero v x).not.2 hx
      simp [hx]; omega
  have SAC := sum_AB v (S1f v j₀) hS1v C
  have SAC' := sum_AB v (S1f v j₀) hS1v C'
  rw [hS0] at SAC SAC'
  -- dominance
  have hd1 : (C'.map (cr' (S1f v j₀))).sum ≤ (C.map (cr' (S1f v j₀))).sum := by
    have := hd v j₀
    rw [dsum (S1f v j₀) C v j₀ (funext fun x => (S1f_eq v j₀ x).symm),
      dsum (S1f v j₀) C' v j₀ (funext fun x => (S1f_eq v j₀ x).symm)] at this
    exact this
  have hd0 : (C'.map (cr' (S0f v j₀))).sum ≤ (C.map (cr' (S0f v j₀))).sum := by
    by_cases hj : j₀ = RepellingPairs.Dev.L10Eq.pred' v
    · have z : ∀ D : Config n, (D.map (cr' (S0f v j₀))).sum = 0 := by
        intro D
        apply Multiset.sum_eq_zero
        intro z hz
        obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hz
        induction s using Sym2.ind with
        | _ x y => simp [cr', RepellingPairs.Dev.L10Eq.cr, S0f_all v j₀ x hj, S0f_all v j₀ y hj]
      rw [z, z]
    · have := hd (RepellingPairs.Dev.L10Eq.pred' v) j₀
      have fe : onSide (RepellingPairs.Dev.L10Eq.pred' v) j₀ = S0f v j₀ :=
        funext fun x => (S0f_eq v j₀ x hj).symm
      rw [dsum (S0f v j₀) C _ _ fe, dsum (S0f v j₀) C' _ _ fe] at this
      exact this
  -- degrees
  have hdC := deg_AL v C
  have hdC' := deg_AL v C'
  have hdv := hdeg v
  have hL : (C.map (cL v)).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hz
    induction s using Sym2.ind with
    | _ x y =>
      simp only [cL, Sym2.lift_mk]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd hs (hloop _)
      · rfl
  have hLp : ∀ s ∈ C', cL v s ≤ (C'.map (cL v)).sum := fun s hs =>
    Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ (Multiset.mem_map_of_mem _ hs)
  have hBp : ∀ s ∈ C', cB v (S1f v j₀) s ≤ (C'.map (cB v (S1f v j₀))).sum := fun s hs =>
    Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ (Multiset.mem_map_of_mem _ hs)
  have hw1 := hBp c1' hc1'
  have hw2 := hLp c1' hc1'
  -- value of the split distances
  have SB' := dist_split_B v w C' c1' hc1' e1' j₀
  have SB'' := fun h => dist_split_B' v w C' c1' hc1' e1' h j₀
  have hu1S : S0f v j₀ u1 = S1f v j₀ u1 := by
    have := congrFun hS0 u1
    simpa [hu1v] using this.symm
  have hBC : S1f v j₀ u1 = false → (C.map (cB v (S1f v j₀))).sum = 0 := by
    intro hf
    have key1 : key v c1 = cdv v u1 := by rw [e1]; exact key_mk v u1 hu1v
    have claim : ∀ y, s(v, y) ∈ C → S1f v j₀ y = true → False := by
      intro y hy hSy
      have hyv : y ≠ v := by rintro rfl; rw [hS1v] at hSy; exact Bool.false_ne_true hSy
      have h1 := hnear _ hy (Sym2.mem_mk_left v y)
      rw [key1, key_mk v y hyv] at h1
      have h2 := (cdv_zero v u1).not.2 hu1v
      simp only [S1f, decide_eq_true_eq, decide_eq_false_iff_not] at hSy hf
      omega
    apply Multiset.sum_eq_zero
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hz
    induction s using Sym2.ind with
    | _ x y =>
      simp only [cB, Sym2.lift_mk]
      split_ifs with h3 h4 h4
      · exfalso; obtain ⟨rfl, h3⟩ := h3; exact claim y hs h3
      · exfalso; obtain ⟨rfl, h3⟩ := h3; exact claim y hs h3
      · exfalso; obtain ⟨rfl, h4⟩ := h4; rw [Sym2.eq_swap] at hs; exact claim x hs h4
      · rfl
  have hBC' : S1f v j₀ w = true → w ≠ v → 1 ≤ (C'.map (cB v (S1f v j₀))).sum := by
    intro h1 h2
    have : 1 ≤ cB v (S1f v j₀) c1' := by
      rw [e1']
      simp only [cB, Sym2.lift_mk]
      simp [h1, h2]
    omega
  have hLC' : w = v → 1 ≤ (C'.map (cL v)).sum := by
    intro h
    have : 1 ≤ cL v c1' := by
      rw [e1', h]
      simp [cL]
    omega
  have hwS : w ≠ v → S0f v j₀ w = S1f v j₀ w := by
    intro hw'
    have := congrFun hS0 w
    simpa [hw'] using this.symm
  by_cases hwv : w = v
  · have h8 := SB'' hwv
    have h9 := hLC' hwv
    rcases (Bool.eq_false_or_eq_true (S1f v j₀ u1)).symm with h | h
    · have := hBC h
      rw [hu1S, h] at SB
      simp only [Bool.false_eq_true, if_false, if_true] at SB
      omega
    · rw [hu1S, h] at SB
      simp only [if_false, if_true] at SB
      omega
  · have e8 := hwS hwv
    rw [e8] at SB'
    rw [hu1S] at SB
    rcases (Bool.eq_false_or_eq_true (S1f v j₀ u1)).symm with h | h <;>
    rcases (Bool.eq_false_or_eq_true (S1f v j₀ w)).symm with h' | h'
    · have := hBC h
      rw [h] at SB; rw [h'] at SB'
      simp only [Bool.false_eq_true, if_false, if_true] at SB SB'
      omega
    · have := hBC h
      have := hBC' h' hwv
      rw [h] at SB; rw [h'] at SB'
      simp only [Bool.false_eq_true, if_false, if_true] at SB SB'
      omega
    · rw [h] at SB; rw [h'] at SB'
      simp only [Bool.false_eq_true, if_false, if_true] at SB SB'
      omega
    · rw [h] at SB; rw [h'] at SB'
      simp only [Bool.false_eq_true, if_false, if_true] at SB SB'
      omega

theorem onSide_swap (i j x : Fin n) (h : i ≠ j) : onSide j i x = !onSide i j x := by
  have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
  rw [RepellingPairs.Dev.L10Eq.onSide_dec, RepellingPairs.Dev.L10Eq.onSide_dec, ← decide_not]
  simp only [decide_eq_decide]
  omega

theorem dist_swap (D : Config n) (i j : Fin n) (h : i ≠ j) : Config.dist D i j = Config.dist D j i := by
  unfold Config.dist
  congr 1
  apply Multiset.map_congr rfl
  intro s _
  induction s using Sym2.ind with
  | _ x y =>
    simp only [chordCross, Sym2.lift_mk, onSide_swap i j x h, onSide_swap i j y h]
    cases onSide i j x <;> cases onSide i j y <;> simp

/-- The cut-by-cut comparison after splitting `v`. Cuts that do not separate `v'` from `v''` are
transported directly; the cuts `(v', j)` and `(i, v')` are handled by `split_dom_B` (and `dist_swap`). -/
theorem split_dom (C C' : Config n) (v : Fin n) (c1 c1' : Sym2 (Fin n))
    (hloop : ∀ a, s(a, a) ∉ C) (hdeg : ∀ t, deg C t = deg C' t) (hd : Dominates C C')
    (hc1 : c1 ∈ C) (hvc1 : v ∈ c1) (hc1' : c1' ∈ C') (hvc1' : v ∈ c1')
    (hnear : ∀ s ∈ C, v ∈ s → key v c1 ≤ key v s)
    (hfar : ∀ s ∈ C', v ∈ s → key v s ≤ key v c1') (hv : 2 ≤ deg C v) :
    Dominates (splitCfg v C (oth v c1) c1) (splitCfg v C' (oth v c1') c1') := by
  intro i j
  by_cases hi : i = Fin.castSucc v <;> by_cases hj : j = Fin.castSucc v
  · subst hi; subst hj
    rw [dist_self_cut]; exact Nat.zero_le _
  · obtain ⟨j₀, rfl⟩ := Fin.exists_succAbove_eq hj
    subst hi
    exact split_dom_B C C' v c1 c1' hloop hdeg hd hc1 hvc1 hc1' hvc1' hnear hv j₀
  · obtain ⟨i₀, rfl⟩ := Fin.exists_succAbove_eq hi
    subst hj
    have hne : gS v i₀ ≠ Fin.castSucc v := gS_ne v i₀
    change Config.dist (splitCfg v C' (oth v c1') c1') (gS v i₀) (Fin.castSucc v) ≤
      Config.dist (splitCfg v C (oth v c1) c1) (gS v i₀) (Fin.castSucc v)
    rw [dist_swap _ _ _ hne, dist_swap _ _ _ hne]
    exact split_dom_B C C' v c1 c1' hloop hdeg hd hc1 hvc1 hc1' hvc1' hnear hv i₀
  · obtain ⟨i₀, rfl⟩ := Fin.exists_succAbove_eq hi
    obtain ⟨j₀, rfl⟩ := Fin.exists_succAbove_eq hj
    have e1 := oth_spec hvc1
    have e1' := oth_spec hvc1'
    have h1 := dist_split_A v _ C c1 hc1 e1 i₀ j₀
    have h2 := dist_split_A v _ C' c1' hc1' e1' i₀ j₀
    change Config.dist (splitCfg v C' (oth v c1') c1') (gS v i₀) (gS v j₀) ≤
      Config.dist (splitCfg v C (oth v c1) c1) (gS v i₀) (gS v j₀)
    rw [h1, h2]
    exact hd i₀ j₀

end RepellingPairs.Dev.Lemma10Dom
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace RepellingPairs.Dev.Lemma10Step

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.Lemma10Proj RepellingPairs.Dev.Lemma10PM
  RepellingPairs.Dev.Lemma10Del RepellingPairs.Dev.Lemma10Split RepellingPairs.Dev.Lemma10Dom

theorem split_step {n : ℕ} (C C' : Config n) (v : Fin n) (hv : 2 ≤ deg C v)
    (hloop : ∀ a, s(a, a) ∉ C) (hdeg : ∀ t, deg C t = deg C' t) (hd : Dominates C C') :
    ∃ (π : Fin (n + 1) → Fin n) (Ĉ Ĉ' : Config (n + 1)), Monotone π ∧ img π Ĉ = C ∧ img π Ĉ' = C' ∧
      (∀ a, s(a, a) ∉ Ĉ) ∧ (∀ t, deg Ĉ t = deg Ĉ' t) ∧ Dominates Ĉ Ĉ' ∧
      ∑ t, deg Ĉ t ^ 2 < ∑ t, deg C t ^ 2 := by
  obtain ⟨c1, hc1, hvc1, hnear⟩ := exists_near C v (exists_at v (by omega))
  obtain ⟨c1', hc1', hvc1', hfar⟩ := exists_far C' v (exists_at v (by rw [← hdeg]; omega))
  have e1 := oth_spec hvc1
  have e1' := oth_spec hvc1'
  refine ⟨v.predAbove, splitCfg v C (oth v c1) c1, splitCfg v C' (oth v c1') c1',
    Fin.predAbove_right_monotone v, split_proj v _ C c1 hc1 e1, split_proj v _ C' c1' hc1' e1',
    split_loopfree v _ C c1 hloop, ?_,
    split_dom C C' v c1 c1' hloop hdeg hd hc1 hvc1 hc1' hvc1' hnear hfar hv, ?_⟩
  · have h1 := deg_split_g v _ C c1 hc1 e1
    have h2 := deg_split_g v _ C' c1' hc1' e1'
    intro t
    by_cases ht : t = Fin.castSucc v
    · subst ht
      rw [deg_split_v1, deg_split_v1]
    · obtain ⟨x, hx⟩ := Fin.exists_succAbove_eq ht
      have hx' : gS v x = t := hx
      subst hx'
      have := h1 x
      have := h2 x
      have := hdeg x
      omega
  · have h1 := deg_split_g v _ C c1 hc1 e1
    rw [Fin.sum_univ_succAbove _ (Fin.castSucc v)]
    change deg (splitCfg v C (oth v c1) c1) (Fin.castSucc v) ^ 2 +
      ∑ x, deg (splitCfg v C (oth v c1) c1) (gS v x) ^ 2 < _
    rw [deg_split_v1]
    have key : ∀ x, deg (splitCfg v C (oth v c1) c1) (gS v x) ^ 2 + (if x = v then 2 * deg C v - 1 else 0) =
        deg C x ^ 2 := by
      intro x
      have := h1 x
      by_cases hx : x = v
      · subst hx
        simp only [if_true] at this ⊢
        obtain ⟨k, hk⟩ : ∃ k, deg C x = k + 1 := ⟨deg C x - 1, by omega⟩
        have e : deg (splitCfg x C (oth x c1) c1) (gS x x) = k := by omega
        rw [e, hk]
        have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        rw [this]; ring
      · simp only [hx, if_false] at this ⊢
        have e : deg (splitCfg v C (oth v c1) c1) (gS v x) = deg C x := by omega
        rw [e]; rfl
    have hs : ∑ x, (deg (splitCfg v C (oth v c1) c1) (gS v x) ^ 2 + (if x = v then 2 * deg C v - 1 else 0)) =
        ∑ x, deg C x ^ 2 := Finset.sum_congr rfl fun x _ => key x
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v] at hs
    simp only [Finset.mem_univ, if_true] at hs
    omega

end RepellingPairs.Dev.Lemma10Step
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Lemma10

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.Lemma10Proj
  RepellingPairs.Dev.Lemma10PM RepellingPairs.Dev.Lemma10Del RepellingPairs.Dev.Lemma10Split RepellingPairs.Dev.Lemma10Step

theorem main (μ : ℕ) : ∀ (n : ℕ) (C C' : Config n), ∑ t, deg C t ^ 2 = μ →
    (∀ a, s(a, a) ∉ C) → (∀ t, deg C t = deg C' t) → Dominates C C' → Reaches C C' := by
  induction μ using Nat.strong_induction_on with
  | _ μ ihμ =>
    intro n
    induction n with
    | zero =>
      intro C C' _ _ _ _
      have : C = C' := Multiset.ext.2 fun s => Sym2.ind (fun x _ => x.elim0) s
      rw [this]
      exact Relation.ReflTransGen.refl
    | succ m ihn =>
      intro C C' hμ hloop hdeg hd
      by_cases hz : ∃ p, deg C p = 0
      · obtain ⟨p, hp⟩ := hz
        obtain ⟨C₀, C₀', e, e', hl, hg, hd0, hs⟩ := delete_step C C' p hp hloop hdeg hd
        have := ihn C₀ C₀' (hs.trans hμ) hl hg hd0
        rw [e, e']
        exact reaches_map _ (Fin.strictMono_succAbove p).monotone this
      · push Not at hz
        by_cases h1 : ∀ t, deg C t = 1
        · exact pm_reaches C C' h1 hdeg hd
        · push Not at h1
          obtain ⟨v, hv⟩ := h1
          have hv2 : 2 ≤ deg C v := by have := hz v; omega
          obtain ⟨π, Ĉ, Ĉ', hπ, e, e', hl, hg, hd', hlt⟩ := split_step C C' v hv2 hloop hdeg hd
          have := ihμ _ (hμ ▸ hlt) _ Ĉ Ĉ' rfl hl hg hd'
          rw [← e, ← e']
          exact reaches_map π hπ this

end RepellingPairs.Dev.Lemma10

namespace RepellingPairs

theorem chk_lemma_10_dominance_implies_uncrossing {n : ℕ} (C C' : Config n)
    (hloop : ∀ a, s(a, a) ∉ C) (hdeg : ∀ t, Config.deg C t = Config.deg C' t)
    (h : Config.StrictlyDominates C C') : Config.Reaches C C' :=
  RepellingPairs.Dev.Lemma10.main _ n C C' rfl hloop hdeg h.1

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_lemma_10_dominance_implies_uncrossing := @RepellingPairs.chk_lemma_10_dominance_implies_uncrossing
