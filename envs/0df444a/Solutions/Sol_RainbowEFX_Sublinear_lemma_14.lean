-- Prove2me | solution 1 for RainbowEFX.Sublinear.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:01:41.97176+00:00
-- url     : https://prove2.me/submissions/d54a8aa4-91be-4bf9-91d0-d20873b402cc

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting
import Theorems.Thm_RainbowEFX_Sublinear_lemma_10

open LittleCharity.EFX RainbowEFX.Sublinear

/-- A walk extracted from `TransGen`, as an ℕ-indexed sequence. -/
theorem REFX_walk_of_transGen' {α : Type} (E : α → α → Prop) {i j : α}
    (h : Relation.TransGen E i j) :
    ∃ (r : ℕ) (c : ℕ → α), c 0 = i ∧ c (r + 1) = j ∧ ∀ k ≤ r, E (c k) (c (k + 1)) := by
  classical
  induction h with
  | single hb =>
    rename_i b
    exact ⟨0, fun k => if k = 0 then i else b, by simp, by simp, by
      intro k hk; have : k = 0 := by omega
      subst this; simpa using hb⟩
  | @tail b c' _ hbc ih =>
    obtain ⟨r, c, h0, hr, hE⟩ := ih
    refine ⟨r + 1, fun k => if k ≤ r + 1 then c k else c', by simp [h0], by simp, ?_⟩
    intro k hk
    by_cases hk' : k ≤ r
    · simp only [show k ≤ r + 1 by omega, show k + 1 ≤ r + 1 by omega, if_true]
      exact hE k hk'
    · have : k = r + 1 := by omega
      subst this
      simp only [le_refl, if_true, show ¬ (r + 1 + 1 ≤ r + 1) by omega, if_false, hr]
      exact hbc

/-- A closed walk through a vertex satisfying `P` yields an injective cycle
`d : Fin (r+1) → α` whose vertex `d 0` satisfies `P`. -/
theorem REFX_simple_cycle_P {α : Type} (E : α → α → Prop) (P : α → Prop) {i : α}
    (hP : P i) (h : Relation.TransGen E i i) :
    ∃ (r : ℕ) (d : Fin (r + 1) → α), Function.Injective d ∧ P (d 0) ∧
      ∀ k, E (d k) (d (finRotate (r + 1) k)) := by
  classical
  have hex : ∃ r, ∃ c : ℕ → α, P (c 0) ∧ c (r + 1) = c 0 ∧ ∀ k ≤ r, E (c k) (c (k + 1)) := by
    obtain ⟨r, c, h0, hr, hE⟩ := REFX_walk_of_transGen' E h
    exact ⟨r, c, h0 ▸ hP, by rw [hr, h0], hE⟩
  set r := Nat.find hex with hrdef
  obtain ⟨c, hcP, hcr, hE⟩ := Nat.find_spec hex
  have hmin : ∀ r' < r, ¬ ∃ c : ℕ → α, P (c 0) ∧ c (r' + 1) = c 0 ∧
      ∀ k ≤ r', E (c k) (c (k + 1)) :=
    fun r' hr' => Nat.find_min hex hr'
  have hinj : ∀ a b, a < b → b ≤ r → c a ≠ c b := by
    intro a b hab hb heq
    apply hmin (r - (b - a)) (by omega)
    refine ⟨fun k => if k ≤ a then c k else c (k + (b - a)), ?_, ?_, ?_⟩
    · simpa using hcP
    · simp only [Nat.zero_le, if_true, show ¬ (r - (b - a) + 1 ≤ a) by omega, if_false]
      rw [show r - (b - a) + 1 + (b - a) = r + 1 by omega]; exact hcr
    · intro k hk
      by_cases hka : k < a
      · simp only [show k ≤ a by omega, show k + 1 ≤ a by omega, if_true]
        exact hE k (by omega)
      · by_cases hka' : k = a
        · subst hka'
          simp only [le_refl, if_true, show ¬ (k + 1 ≤ k) by omega, if_false]
          rw [heq, show k + 1 + (b - k) = b + 1 by omega]
          exact hE b hb
        · simp only [show ¬ k ≤ a by omega, show ¬ (k + 1 ≤ a) by omega, if_false]
          rw [show k + 1 + (b - a) = k + (b - a) + 1 by omega]
          exact hE _ (by omega)
  refine ⟨r, fun k => c k.val, ?_, by simpa using hcP, ?_⟩
  · intro a b hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact hinj a b h (by omega) hab
    · exact hinj b a h (by omega) hab.symm
  · intro k
    have := hE k.val (by omega)
    show E (c k.val) (c (finRotate (r + 1) k).val)
    rw [coe_finRotate]
    by_cases hk : k = Fin.last r
    · rw [if_pos hk]
      have hk' : k.val = r := by rw [hk]; simp
      rw [hk'] at this ⊢
      rw [hcr] at this
      exact this
    · rw [if_neg hk]
      exact this

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (d : ℕ) (hstar : Star ε v X) (src : Fin n → Fin n) (hsrc : IsSourceAssignment v X src)
    (r : ℕ) (c : Fin r → Fin m × Fin n) (hc : ∀ i, GCVertex ε v X d src (c i))
    (hcyc : IsRainbowCycle Prod.fst (GCAdj ε v X src) c) :
    ∃ X' : Fin n → Finset (Fin m), IsPartialAllocation X' ∧ IsAlphaEFX (1 - ε) v X' ∧
      StronglyParetoDominates ε v X' X := by
  classical
  have hε1 : ε < 1 := by linarith
  obtain ⟨hr2, hfinj, hadj⟩ := hcyc
  obtain ⟨R, rfl⟩ : ∃ R, r = R + 1 := ⟨r - 1, by omega⟩
  -- the champion `a k` of the edge `c k → c (k+1)`
  choose a b ha hb hsa hsb hmea using hadj
  -- the walk of sources along the cycle
  let Rel : Fin n → Fin n → Prop := fun x y =>
    ∃ k, (c k).2 = x ∧ (c (finRotate (R + 1) k)).2 = y
  have hrot : ∀ j (hj : j + 1 < R + 1),
      finRotate (R + 1) ⟨j, by omega⟩ = ⟨j + 1, hj⟩ := by
    intro j hj
    apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hchain : ∀ j (hj : j < R + 1),
      Relation.TransGen Rel (c 0).2 (c (finRotate (R + 1) ⟨j, hj⟩)).2 := by
    intro j
    induction j with
    | zero => intro hj; exact Relation.TransGen.single ⟨0, rfl, rfl⟩
    | succ j ih =>
      intro hj
      have := ih (by omega)
      rw [hrot j hj] at this
      exact this.tail ⟨⟨j + 1, hj⟩, rfl, rfl⟩
  have hcl : Relation.TransGen Rel (c 0).2 (c 0).2 := by
    have := hchain R (by omega)
    rwa [show (⟨R, by omega⟩ : Fin (R + 1)) = Fin.last R from rfl, finRotate_last] at this
  obtain ⟨q, e, heinj, -, heE⟩ := REFX_simple_cycle_P Rel (fun _ => True) trivial hcl
  choose k hk1 hk2 using heE
  have hkinj : Function.Injective k := by
    intro j j' h
    apply heinj
    rw [← hk1 j, ← hk1 j', h]
  have hsrc_a : ∀ j, src (a (k j)) = e j := fun j => (hsa (k j)).trans (hk1 j)
  refine lemma_10 v hv ε hε0 hε1 X hX hEFX (q + 1) (by omega) e
    (fun j => (c (k ((finRotate (q + 1)).symm j))).1) (fun j => a (k j)) heinj ?_ ?_ ?_ ?_ ?_ ?_
  · intro j j' h
    exact (finRotate (q + 1)).symm.injective (hkinj (hfinj h))
  · intro j j' h
    apply heinj
    rw [← hsrc_a j, ← hsrc_a j']
    exact congrArg src h
  · intro j
    rw [← hsrc_a j]
    exact (hsrc _).1
  · intro j
    exact (Finset.mem_filter.mp (hc _).1).1
  · intro j
    rw [← hsrc_a j]
    exact (hsrc _).2
  · intro j
    simp only [Equiv.symm_apply_apply]
    have := hmea (k j)
    rwa [hk2 j] at this
