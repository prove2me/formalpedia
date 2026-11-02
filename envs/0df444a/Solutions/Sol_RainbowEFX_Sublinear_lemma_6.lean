-- Prove2me | solution 1 for RainbowEFX.Sublinear.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:52:24.671204+00:00
-- url     : https://prove2.me/submissions/06bdd1da-48c0-49cb-aeef-d5024bfd527d

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

open LittleCharity.EFX RainbowEFX.Sublinear

/-- A closed walk through `i` extracted from `TransGen`, as an ℕ-indexed sequence. -/
theorem REFX_walk_of_transGen {α : Type} (E : α → α → Prop) {i j : α}
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

/-- A cycle in a relation yields an injective cycle `d : Fin (r+1) → α`. -/
theorem REFX_simple_cycle {α : Type} (E : α → α → Prop) {i : α}
    (h : Relation.TransGen E i i) :
    ∃ (r : ℕ) (d : Fin (r + 1) → α), Function.Injective d ∧
      ∀ k, E (d k) (d (finRotate (r + 1) k)) := by
  classical
  have hex : ∃ r, ∃ c : ℕ → α, c (r + 1) = c 0 ∧ ∀ k ≤ r, E (c k) (c (k + 1)) := by
    obtain ⟨r, c, h0, hr, hE⟩ := REFX_walk_of_transGen E h
    exact ⟨r, c, by rw [hr, h0], hE⟩
  let r := Nat.find hex
  obtain ⟨c, hcr, hE⟩ := Nat.find_spec hex
  have hmin : ∀ r' < r, ¬ ∃ c : ℕ → α, c (r' + 1) = c 0 ∧ ∀ k ≤ r', E (c k) (c (k + 1)) :=
    fun r' hr' => Nat.find_min hex hr'
  have hinj : ∀ a b, a ≤ r → b ≤ r → c a = c b → a = b := by
    intro a b ha hb hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · apply hmin (b - a - 1) (by omega)
      refine ⟨fun k => c (a + k), ?_, ?_⟩
      · simp only [Nat.add_zero]
        rw [show a + (b - a - 1 + 1) = b by omega]; exact hab.symm
      · intro k hk
        show E (c (a + k)) (c (a + (k + 1)))
        rw [show a + (k + 1) = a + k + 1 by omega]
        exact hE _ (by omega)
    · apply hmin (a - b - 1) (by omega)
      refine ⟨fun k => c (b + k), ?_, ?_⟩
      · simp only [Nat.add_zero]
        rw [show b + (a - b - 1 + 1) = a by omega]; exact hab
      · intro k hk
        show E (c (b + k)) (c (b + (k + 1)))
        rw [show b + (k + 1) = b + k + 1 by omega]
        exact hE _ (by omega)
  refine ⟨r, fun k => c k.val, ?_, ?_⟩
  · intro a b hab
    exact Fin.ext (hinj a b (by omega) (by omega) hab)
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
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (hcyc : ∃ i, Relation.TransGen (Envies v X) i i) :
    ∃ X' : Fin n → Finset (Fin m), IsPartialAllocation X' ∧ IsAlphaEFX (1 - ε) v X' ∧
      (∀ i, v i (X i) ≤ v i (X' i)) ∧ EnvyAcyclic v X' ∧ pool X' = pool X := by
  classical
  set A : Finset (Fin n → Finset (Fin m)) := Finset.univ.filter (fun Y =>
    IsPartialAllocation Y ∧ IsAlphaEFX (1 - ε) v Y ∧ (∀ i, v i (X i) ≤ v i (Y i)) ∧
      pool Y = pool X) with hA
  have hXA : X ∈ A := by
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hX, hEFX, fun i => le_rfl, trivial⟩
  obtain ⟨Y, hYA, hYmax⟩ := Finset.exists_max_image A (welfare v) ⟨X, hXA⟩
  have hYA' := hYA
  simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hYA'
  obtain ⟨hYP, hYE, hYv, hYpool⟩ := hYA'
  refine ⟨Y, hYP, hYE, hYv, ?_, hYpool⟩
  intro i hi
  obtain ⟨r, d, hdinj, hdE⟩ := REFX_simple_cycle (Envies v Y) hi
  -- rotate the bundles along the cycle
  set σ : Equiv.Perm (Fin n) :=
    (finRotate (r + 1)).extendDomain (Equiv.ofInjective d hdinj) with hσ
  have hσd : ∀ k, σ (d k) = d (finRotate (r + 1) k) := by
    intro k
    have := Equiv.Perm.extendDomain_apply_image (finRotate (r + 1))
      (Equiv.ofInjective d hdinj) k
    simpa using this
  have hσout : ∀ j, (¬ ∃ k, d k = j) → σ j = j := by
    intro j hj
    apply Equiv.Perm.extendDomain_apply_not_subtype
    simpa [Set.mem_range] using hj
  set Y' : Fin n → Finset (Fin m) := fun j => Y (σ j) with hY'
  have hge : ∀ j, v j (Y j) ≤ v j (Y' j) := by
    intro j
    by_cases hj : ∃ k, d k = j
    · obtain ⟨k, rfl⟩ := hj
      simp only [hY', hσd]
      exact (hdE k).le
    · simp [hY', hσout j hj]
  have hgt : v (d 0) (Y (d 0)) < v (d 0) (Y' (d 0)) := by
    simp only [hY', hσd]; exact hdE 0
  have hY'A : Y' ∈ A := by
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, fun j => (hYv j).trans (hge j), ?_⟩
    · intro a b hab
      exact hYP (fun h => hab (σ.injective h))
    · intro a b g hg
      exact (hYE a (σ b) g hg).trans (hge a)
    · rw [← hYpool]
      unfold pool
      congr 1
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hY']
      constructor
      · rintro ⟨j, hj⟩; exact ⟨σ j, hj⟩
      · rintro ⟨j, hj⟩; exact ⟨σ.symm j, by simpa using hj⟩
  have hw : welfare v Y < welfare v Y' := by
    unfold welfare
    exact Finset.sum_lt_sum (fun j _ => hge j) ⟨d 0, Finset.mem_univ _, hgt⟩
  have := hYmax Y' hY'A
  linarith
