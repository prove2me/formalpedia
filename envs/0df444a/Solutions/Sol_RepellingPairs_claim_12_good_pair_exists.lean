-- Prove2me | solution 1 for RepellingPairs.claim_12_good_pair_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:00:51.556247+00:00
-- url     : https://prove2.me/submissions/62028bce-be46-47ac-909d-a1c9c66bf06e

import Mathlib
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair

section
set_option autoImplicit false

namespace RepellingPairs.Dev.CutCount

open RepellingPairs RepellingPairs.Config
open Classical

variable {n : ℕ}

/-- number of points of `S` whose partner is outside `S` -/
noncomputable def cr (C : PerfectMatching n) (S : Fin n → Prop) : ℕ :=
  (Finset.univ.filter fun a => S a ∧ ¬ S (C.partner a)).card

/-- the same count from the outside -/
noncomputable def cr' (C : PerfectMatching n) (S : Fin n → Prop) : ℕ :=
  (Finset.univ.filter fun a => ¬ S a ∧ S (C.partner a)).card

theorem cr'_eq (C : PerfectMatching n) (S : Fin n → Prop) : cr' C S = cr C S := by
  unfold cr' cr
  apply Finset.card_bij (fun a _ => C.partner a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [C.involutive a]; exact ⟨ha.2, ha.1⟩
  · intro a _ b _ h
    exact C.involutive.injective h
  · intro b hb
    refine ⟨C.partner b, ?_, C.involutive b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [C.involutive b]; exact ⟨hb.2, hb.1⟩

theorem sum_cross (C : PerfectMatching n) (S : Fin n → Prop) :
    (∑ x : Fin n, (if (S x ↔ S (C.partner x)) then 0 else 1)) = 2 * cr C S := by
  have h1 : (∑ x : Fin n, (if (S x ↔ S (C.partner x)) then 0 else 1)) =
      (∑ x : Fin n, (if S x ∧ ¬ S (C.partner x) then 1 else 0)) +
      (∑ x : Fin n, (if ¬ S x ∧ S (C.partner x) then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h1 : S x <;> by_cases h2 : S (C.partner x) <;> simp [h1, h2]
  rw [h1]
  have h2 : (∑ x : Fin n, (if S x ∧ ¬ S (C.partner x) then 1 else 0)) = cr C S := by
    unfold cr; rw [Finset.sum_boole]; simp
  have h3 : (∑ x : Fin n, (if ¬ S x ∧ S (C.partner x) then 1 else 0)) = cr' C S := by
    unfold cr'; rw [Finset.sum_boole]; simp
  rw [h2, h3, cr'_eq]; ring

theorem dist_eq_cr (C : PerfectMatching n) (i j : Fin n) :
    Config.dist C.config i j = cr C (fun a => onSide i j a = true) := by
  have key : 2 * Config.dist C.config i j =
      ∑ x : Fin n, (if (onSide i j x = true ↔ onSide i j (C.partner x) = true) then 0 else 1) := by
    unfold Config.dist PerfectMatching.config
    set g : Fin n → Sym2 (Fin n) := fun x => s(x, C.partner x) with hg
    have hs : ((Finset.univ.image g).val.map (chordCross i j)).sum =
        ∑ c ∈ Finset.univ.image g, chordCross i j c := rfl
    rw [hs]
    have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
      (t := Finset.univ.image g) (g := g)
      (fun x _ => Finset.mem_image_of_mem g (Finset.mem_univ x)) (fun x => chordCross i j (g x))
    have hF : ∀ c ∈ Finset.univ.image g,
        (∑ x ∈ Finset.univ.filter (fun x => g x = c), chordCross i j (g x)) = 2 * chordCross i j c := by
      intro c hc
      obtain ⟨x0, _, rfl⟩ := Finset.mem_image.1 hc
      have hfil : Finset.univ.filter (fun x => g x = g x0) = {x0, C.partner x0} := by
        ext x
        simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Sym2.eq_iff]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl ⟨h, by rw [h]⟩
          · exact Or.inr ⟨h, by rw [h, C.involutive x0]⟩
      rw [hfil, Finset.sum_pair (Ne.symm (C.ne_self x0))]
      have : g (C.partner x0) = g x0 := by
        simp only [hg, C.involutive x0, Sym2.eq_swap]
      rw [this]; ring
    have h2 : ∑ c ∈ Finset.univ.image g, 2 * chordCross i j c = ∑ x : Fin n, chordCross i j (g x) :=
      (Finset.sum_congr rfl hF).symm.trans hfib
    rw [Finset.mul_sum, h2]
    apply Finset.sum_congr rfl
    intro x _
    simp only [hg, chordCross, Sym2.lift_mk]
    by_cases h1 : onSide i j x = true <;> by_cases h2 : onSide i j (C.partner x) = true <;>
      simp_all
  have h0 := sum_cross C (fun a => onSide i j a = true)
  have h : 2 * Config.dist C.config i j = 2 * cr C (fun a => onSide i j a = true) := by
    rw [key, ← h0]
    apply Finset.sum_congr rfl
    intro x _
    congr
  omega

/-- strict inequality from an injection with a missing point (outside form) -/
theorem cr_lt (C C' : PerfectMatching n) (S : Fin n → Prop)
    (h : ∀ a, ¬ S a → S (C.partner a) → S (C'.partner a))
    (e : Fin n) (he : ¬ S e) (he1 : S (C'.partner e)) (he2 : ¬ S (C.partner e)) :
    cr C S < cr C' S := by
  rw [← cr'_eq, ← cr'_eq]
  unfold cr'
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨e, by simp [he, he1], by simp [he, he2]⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨ha.1, h a ha.1 ha.2⟩

theorem onSide_iff (i j a : Fin n) : onSide i j a = true ↔
    (i.val ≤ j.val ∧ i.val < a.val ∧ a.val ≤ j.val) ∨
      (j.val < i.val ∧ (i.val < a.val ∨ a.val ≤ j.val)) := by
  unfold onSide
  split_ifs with h <;> simp only [decide_eq_true_eq, Fin.le_def, Fin.lt_def] at h ⊢ <;> omega

/-- the arc of `m` points starting at `s` (`s ≤ n`, wrapping around) -/
def ar (n s m : ℕ) (a : Fin n) : Prop :=
  (s ≤ a.val ∧ a.val < s + m) ∨ (a.val < s ∧ a.val + n < s + m)

theorem cr_congr (C : PerfectMatching n) (S T : Fin n → Prop) (h : ∀ a, S a ↔ T a) :
    cr C S = cr C T := by
  have : S = T := funext fun a => propext (h a)
  rw [this]

theorem dom_arc (C C' : PerfectMatching n) (h : Config.Dominates C.config C'.config)
    (S : Fin n → Prop) (s m : ℕ) (hs : s ≤ n) (hm : m < n)
    (hS : ∀ a, S a ↔ ar n s m a) : cr C' S ≤ cr C S := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have h0 : ∀ D : PerfectMatching n, cr D S = 0 := by
      intro D
      unfold cr
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a _ ha
      have := (hS a).1 ha.1
      unfold ar at this; omega
    rw [h0, h0]
  · have hn : 0 < n := by omega
    let i : Fin n := ⟨if s = 0 then n - 1 else s - 1, by split_ifs <;> omega⟩
    let j : Fin n := ⟨if s + m - 1 < n then s + m - 1 else s + m - 1 - n, by split_ifs <;> omega⟩
    have hij : ∀ a, S a ↔ (fun a => onSide i j a = true) a := by
      intro a
      show _ ↔ onSide i j a = true
      rw [onSide_iff, hS a]
      unfold ar
      simp only [i, j]
      split_ifs <;> omega
    rw [cr_congr C S _ hij, cr_congr C' S _ hij, ← dist_eq_cr, ← dist_eq_cr]
    exact h i j

/-- strictly inside the clockwise arc from `u` to `v` -/
def oa (u v a : Fin n) : Prop :=
  (u.val < v.val ∧ u.val < a.val ∧ a.val < v.val) ∨ (v.val < u.val ∧ (u.val < a.val ∨ a.val < v.val))

theorem oa_ar (u v : Fin n) (huv : u ≠ v) :
    ∃ s m : ℕ, s ≤ n ∧ m < n ∧ ∀ a, oa u v a ↔ ar n s m a := by
  refine ⟨u.val + 1, if u.val < v.val then v.val - u.val - 1 else v.val + n - u.val - 1, by omega, ?_, ?_⟩
  · have := u.2; have := v.2
    have : u.val ≠ v.val := fun h => huv (Fin.ext h)
    split_ifs <;> omega
  · intro a
    have : u.val ≠ v.val := fun h => huv (Fin.ext h)
    have := a.2
    unfold oa ar
    split_ifs <;> omega

end RepellingPairs.Dev.CutCount
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Claim12

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.CutCount

variable {n : ℕ}

theorem step12 (C C' : PerfectMatching n) (hno : ∀ x y, ¬ IsGoodPair C C' x y)
    (x : Fin n) (u v : Fin n)
    (huv : (u = x ∧ v = C.partner x) ∨ (u = C.partner x ∧ v = x))
    (hC' : oa u v (C'.partner x)) (a : Fin n) (ha : ¬ oa u v a) (hCa : oa u v (C.partner a)) :
    oa u v (C'.partner a) := by
  have G : ∀ p q : Fin n, ChordsCross p (C.partner p) q (C.partner q) →
      OnDifferentSides p (C.partner p) q (C'.partner p) →
      (InSegment p (C.partner p) (C'.partner p) (C.partner q) ∨
        InSegment p (C.partner p) (C'.partner p) (C'.partner q)) → False :=
    fun p q h1 h2 h3 => hno p q ⟨h1, h2, h3⟩
  have iC := C.involutive a
  have iCx := C.involutive x
  have hxa : a ≠ x := by
    rintro rfl
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> subst u v <;> simp [oa] at hCa <;> omega
  have hxa' : a ≠ C.partner x := by
    rintro rfl
    rw [C.involutive] at hCa
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> subst u v <;> simp [oa] at hCa <;> omega
  have hj1 : C.partner a ≠ C.partner x := fun h => hxa (C.involutive.injective h)
  have hj2 : C.partner a ≠ x := fun h => hxa' (by rw [← h, C.involutive])
  have hj3 : C'.partner a ≠ C'.partner x := fun h => hxa (C'.involutive.injective h)
  have hj4 : C'.partner a ≠ x := by
    intro h
    apply ha
    have : a = C'.partner x := by rw [← h, C'.involutive]
    rw [this]; exact hC'
  have hn1 := C.ne_self x
  have hn2 := C.ne_self a
  have hn3 := C'.ne_self a
  have hn4 := C'.ne_self x
  by_contra hc
  rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst u v
    -- the cut is the arc from `x` to `C x`
    have hca : oa x (C'.partner x) (C.partner a) := by
      by_contra hh
      simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff] at hC' ha hCa hc hxa hxa' hj1 hj2 hj3 hj4 hn1 hn2 hn3 hn4 hh
      first
      | exact G x a (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
      | exact G a x (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
      | exact G a (C.partner x) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
    simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff] at hC' ha hCa hc hxa hxa' hj1 hj2 hj3 hj4 hn1 hn2 hn3 hn4 hca
    have hcl : oa a x (C'.partner a) ∨ oa (C.partner x) a (C'.partner a) ∨ C'.partner a = C.partner x := by
      simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff]; grind (splits := 200)
    simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff] at hcl
    rcases hcl with hcl | hcl | hcl <;>
      first
      | exact G x a (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
      | exact G a x (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
      | exact G a (C.partner x) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
  · subst u v
    -- the cut is the arc from `C x` to `x`
    have hca : oa (C'.partner x) x (C.partner a) := by
      by_contra hh
      simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff] at hC' ha hCa hc hxa hxa' hj1 hj2 hj3 hj4 hn1 hn2 hn3 hn4 hh
      first
      | exact G x a (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
      | exact G a x (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
      | exact G a (C.partner x) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
    simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff] at hC' ha hCa hc hxa hxa' hj1 hj2 hj3 hj4 hn1 hn2 hn3 hn4 hca
    have hcl : oa x a (C'.partner a) ∨ oa a (C.partner x) (C'.partner a) ∨ C'.partner a = C.partner x := by
      simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff]; grind (splits := 200)
    simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff] at hcl
    rcases hcl with hcl | hcl | hcl <;>
      first
      | exact G x a (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
      | exact G a x (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))
      | exact G a (C.partner x) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200)) (by simp only [Config.ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff, iCx]; grind (splits := 200))

end RepellingPairs.Dev.Claim12

namespace RepellingPairs

open RepellingPairs.Dev.Claim12 RepellingPairs.Dev.CutCount

theorem chk_claim_12_good_pair_exists {n : ℕ} (C C' : PerfectMatching n)
    (h : Config.StrictlyDominates C.config C'.config) :
    ∃ x y, IsGoodPair C C' x y := by
  by_contra hno
  push_neg at hno
  obtain ⟨hdom, ⟨i0, j0, hlt⟩⟩ := h
  have hx : ∃ x, C.partner x ≠ C'.partner x := by
    by_contra hall
    push_neg at hall
    have : C.config = C'.config := by
      unfold PerfectMatching.config
      simp only [hall]
    rw [this] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨x, hx⟩ := hx
  have hn1 := C.ne_self x
  have hn4 := C'.ne_self x
  have hori : ∃ u v, ((u = x ∧ v = C.partner x) ∨ (u = C.partner x ∧ v = x)) ∧ oa u v (C'.partner x) := by
    by_cases h1 : oa x (C.partner x) (C'.partner x)
    · exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, h1⟩
    · refine ⟨C.partner x, x, Or.inr ⟨rfl, rfl⟩, ?_⟩
      simp only [oa, ne_eq, Fin.ext_iff] at *
      omega
  obtain ⟨u, v, huv, hC'⟩ := hori
  have hne : u ≠ v := by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun h => hn1 h.symm
    · exact hn1
  obtain ⟨s, m, hs, hm, hS⟩ := oa_ar u v hne
  have hle := dom_arc C C' hdom (oa u v) s m hs hm hS
  have hlt2 : cr C (oa u v) < cr C' (oa u v) := by
    apply cr_lt C C' (oa u v) _ x
    · rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff] at hn1 ⊢ <;> omega
    · exact hC'
    · rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff] at hn1 ⊢ <;> omega
    · intro a ha hCa
      exact step12 C C' hno x u v huv hC' a ha hCa
  omega

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_claim_12_good_pair_exists := @RepellingPairs.chk_claim_12_good_pair_exists
