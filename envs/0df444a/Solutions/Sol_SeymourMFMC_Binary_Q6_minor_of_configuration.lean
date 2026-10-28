-- Prove2me | solution 1 for SeymourMFMC.Binary.Q6_minor_of_configuration
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:00:26.230721+00:00
-- url     : https://prove2.me/submissions/34c9a87d-fd98-49be-9acc-6768d8e4efff

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Linarith
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsCircuit
import Definitions.Def_SeymourMFMC_Binary_HasQ6Minor
import Theorems.Thm_SeymourMFMC_Binary_parity_decomposition

open SeymourMFMC.Binary

private lemma card_sdiff_inter_add_inter {α : Type*} [DecidableEq α]
    (X Y B : Finset α) :
    ((X \ Y) ∩ B).card + ((X ∩ Y) ∩ B).card = (X ∩ B).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.union_inter_distrib_right, Finset.sdiff_union_inter]
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_inter, Finset.mem_sdiff] at hx1
    rw [Finset.mem_inter, Finset.mem_inter] at hx2
    exact hx1.1.2 hx2.1.2

private lemma card_symmDiff_inter {α : Type*} [DecidableEq α]
    (X Y B : Finset α) :
    (symmDiff X Y ∩ B).card + 2 * ((X ∩ Y) ∩ B).card = (X ∩ B).card + (Y ∩ B).card := by
  have h1 := card_sdiff_inter_add_inter X Y B
  have h2 := card_sdiff_inter_add_inter Y X B
  rw [Finset.inter_comm Y X] at h2
  have h3 : (symmDiff X Y ∩ B).card = ((X \ Y) ∩ B).card + ((Y \ X) ∩ B).card := by
    rw [Finset.symmDiff_def, Finset.union_inter_distrib_right, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_inter, Finset.mem_sdiff] at hx1 hx2
    exact hx1.1.2 hx2.1.1
  omega

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

private def C6 : Finset (Finset (Fin 6)) :=
  {{0, 1, 2, 3}, {0, 1, 4, 5}, {2, 3, 4, 5}}

private def A0 : Finset (Fin 6) :=
  {0, 2, 4}

private lemma C6_not_disjoint :
    ∀ S₁ ∈ C6, ∀ S₂ ∈ C6, ¬ Disjoint S₁ S₂ := by decide

private lemma C6_card :
    ∀ S ∈ C6, S.card = 4 := by decide

private lemma C6_symmDiff_mem_Q6 :
    ∀ S ∈ C6, symmDiff A0 S ∈ Q6 := by decide

private lemma A0_mem_Q6 : A0 ∈ Q6 := by decide

private lemma Q6_card :
    ∀ Q ∈ Q6, Q.card = 3 := by decide

private lemma Q6_cases :
    ∀ Q ∈ Q6, Q = A0 ∨ ∃ S ∈ C6, Q = symmDiff A0 S := by decide

private lemma univ_fin3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide

private lemma univ_fin6 : (Finset.univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := by decide

private lemma fin3_lt_cases (i j : Fin 3) (hij : i < j) :
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by
  revert i j
  decide

private lemma finset_map_symmDiff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (S₁ S₂ : Finset α) :
    symmDiff (S₁.map f) (S₂.map f) = (symmDiff S₁ S₂).map f := by
  rw [Finset.symmDiff_def, Finset.symmDiff_def, Finset.map_union, Finset.map_sdiff,
    Finset.map_sdiff]

theorem solution {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (x y : Fin 3 → α) (A : Finset α) (hA : A ∈ L)
    (hcard : (Finset.univ.image x ∪ Finset.univ.image y).card = 6)
    (hZ : Finset.univ.image x ∪ Finset.univ.image y ⊆ ground L)
    (hcirc : ∀ i j : Fin 3, i < j → IsCircuit L {x i, y i, x j, y j})
    (honly : ∀ C ⊆ Finset.univ.image x ∪ Finset.univ.image y, IsCircuit L C →
      ∃ i j : Fin 3, i < j ∧ C = {x i, y i, x j, y j})
    (hA_meets : ∀ i : Fin 3, (x i ∈ A ∧ y i ∉ A) ∨ (y i ∈ A ∧ x i ∉ A))
    (hA_min : ∀ A' ∈ L, A' ⊆ A ∪ (Finset.univ.image x ∪ Finset.univ.image y) →
      A' \ (Finset.univ.image x ∪ Finset.univ.image y) =
        A \ (Finset.univ.image x ∪ Finset.univ.image y)) :
    HasQ6Minor L := by
  let Z := Finset.univ.image x ∪ Finset.univ.image y
  let u : Fin 3 → α := fun i => if x i ∈ A then x i else y i
  let v : Fin 3 → α := fun i => if x i ∈ A then y i else x i
  have huA : ∀ i : Fin 3, u i ∈ A := by
    intro i
    rcases hA_meets i with ⟨hx, hy⟩ | ⟨hy, hx⟩ <;> simp [u, hx, hy]
  have hvA : ∀ i : Fin 3, v i ∉ A := by
    intro i
    rcases hA_meets i with ⟨hx, hy⟩ | ⟨hy, hx⟩ <;> simp [v, hx, hy]
  have huv_pair : ∀ i : Fin 3, ({u i, v i} : Finset α) = {x i, y i} := by
    intro i
    rcases hA_meets i with ⟨hx, _⟩ | ⟨_, hx⟩
    · simp [u, v, hx]
    · simp [u, v, hx, Finset.pair_comm]
  have huv_quad : ∀ i j : Fin 3, ({u i, v i, u j, v j} : Finset α) = {x i, y i, x j, y j} := by
    intro i j
    have h1 := Finset.ext_iff.mp (huv_pair i)
    have h2 := Finset.ext_iff.mp (huv_pair j)
    ext a
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 ⊢
    rcases h1 a with ⟨h1l, h1r⟩
    rcases h2 a with ⟨h2l, h2r⟩
    constructor
    · rintro (rfl | rfl | h)
      · rcases h1l (Or.inl rfl) with h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h)]
      · rcases h1l (Or.inr rfl) with h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h)]
      · exact Or.inr (Or.inr (h2l h))
    · rintro (rfl | rfl | h)
      · rcases h1r (Or.inl rfl) with h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h)]
      · rcases h1r (Or.inr rfl) with h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h)]
      · exact Or.inr (Or.inr (h2r h))
  let g : Fin 6 → α := fun k =>
    if k = 0 then u 0
    else if k = 1 then v 0
    else if k = 2 then u 1
    else if k = 3 then v 1
    else if k = 4 then u 2
    else v 2
  have hg_img : Finset.univ.image g = Z := by
    change Finset.univ.image g = Finset.univ.image x ∪ Finset.univ.image y
    rw [univ_fin6, univ_fin3]
    have h0 := Finset.ext_iff.mp (huv_pair 0)
    have h1 := Finset.ext_iff.mp (huv_pair 1)
    have h2 := Finset.ext_iff.mp (huv_pair 2)
    ext a
    simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1 h2
    simp only [Finset.image_insert, Finset.image_singleton, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, g]
    rcases h0 a with ⟨h0l, h0r⟩
    rcases h1 a with ⟨h1l, h1r⟩
    rcases h2 a with ⟨h2l, h2r⟩
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · rcases h0l (Or.inl rfl) with h | h <;> [exact Or.inl (Or.inl h); exact Or.inr (Or.inl h)]
      · rcases h0l (Or.inr rfl) with h | h <;> [exact Or.inl (Or.inl h); exact Or.inr (Or.inl h)]
      · rcases h1l (Or.inl rfl) with h | h <;>
          [exact Or.inl (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inl h))]
      · rcases h1l (Or.inr rfl) with h | h <;>
          [exact Or.inl (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inl h))]
      · rcases h2l (Or.inl rfl) with h | h <;>
          [exact Or.inl (Or.inr (Or.inr h)); exact Or.inr (Or.inr (Or.inr h))]
      · rcases h2l (Or.inr rfl) with h | h <;>
          [exact Or.inl (Or.inr (Or.inr h)); exact Or.inr (Or.inr (Or.inr h))]
    · rintro ((rfl | rfl | rfl) | (rfl | rfl | rfl))
      · rcases h0r (Or.inl rfl) with h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h)]
      · rcases h1r (Or.inl rfl) with h | h <;>
          [exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr (Or.inl h)))]
      · rcases h2r (Or.inl rfl) with h | h <;>
          [exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))));
           exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))]
      · rcases h0r (Or.inr rfl) with h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h)]
      · rcases h1r (Or.inr rfl) with h | h <;>
          [exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr (Or.inl h)))]
      · rcases h2r (Or.inr rfl) with h | h <;>
          [exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))));
           exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))]
  have hg_inj : Function.Injective g := by
    have hcard_g : (Finset.univ.image g).card = (Finset.univ : Finset (Fin 6)).card := by
      rw [hg_img, hcard]
      decide
    have hinjOn := Finset.injOn_of_card_image_eq hcard_g
    intro k₁ k₂ hk
    exact hinjOn (Finset.mem_univ k₁) (Finset.mem_univ k₂) hk
  let f : Fin 6 ↪ α := ⟨g, hg_inj⟩
  have hZ_map : Z = Finset.univ.map f := by
    rw [← hg_img, Finset.map_eq_image]
    rfl
  have hAZ : A ∩ Z = A0.map f := by
    ext a
    simp only [Finset.mem_inter, hZ_map, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨haA, k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      have hk6 : k ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) := univ_fin6 ▸ Finset.mem_univ k
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk6
      rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · exfalso; exact hvA 0 haA
      · decide
      · exfalso; exact hvA 1 haA
      · decide
      · exfalso; exact hvA 2 haA
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, k, rfl⟩
      simp only [A0, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · exact huA 0
      · exact huA 1
      · exact huA 2
  have hC01 : ({0, 1, 2, 3} : Finset (Fin 6)).map f = {x 0, y 0, x 1, y 1} := by
    rw [← huv_quad 0 1]
    ext a
    simp [f, g]
  have hC02 : ({0, 1, 4, 5} : Finset (Fin 6)).map f = {x 0, y 0, x 2, y 2} := by
    rw [← huv_quad 0 2]
    ext a
    simp [f, g]
  have hC12 : ({2, 3, 4, 5} : Finset (Fin 6)).map f = {x 1, y 1, x 2, y 2} := by
    rw [← huv_quad 1 2]
    ext a
    simp [f, g]
  have hC6_circ : ∀ S ∈ C6, IsCircuit L (S.map f) := by
    intro S hS
    simp only [C6, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl
    · rw [hC01]; exact hcirc 0 1 (by decide)
    · rw [hC02]; exact hcirc 0 2 (by decide)
    · rw [hC12]; exact hcirc 1 2 (by decide)
  have hC6_only : ∀ C ⊆ Z, IsCircuit L C → ∃ S ∈ C6, C = S.map f := by
    intro C hCZ hCc
    obtain ⟨i, j, hij, rfl⟩ := honly C hCZ hCc
    rcases fin3_lt_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨{0, 1, 2, 3}, by decide, hC01.symm⟩
    · exact ⟨{0, 1, 4, 5}, by decide, hC02.symm⟩
    · exact ⟨{2, 3, 4, 5}, by decide, hC12.symm⟩
  have hcycle_sub_Z : ∀ W ⊆ Z, (∀ B ∈ blocker L, Even (W ∩ B).card) →
      W = ∅ ∨ ∃ S ∈ C6, W = S.map f := by
    intro W hWZ heven
    obtain ⟨Cs, hCs1, hCs2, hCs3⟩ :=
      (parity_decomposition L hL hbin W (hWZ.trans hZ)).1 heven
    rcases Cs.eq_empty_or_nonempty with rfl | ⟨C₀, hC₀⟩
    · left
      rw [← hCs3, Finset.sup_empty]
      rfl
    · right
      have hC₀Z : C₀ ⊆ Z := (Finset.le_sup (f := id) hC₀).trans (hCs3.le.trans hWZ)
      obtain ⟨S₀, hS₀, hC₀eq⟩ := hC6_only C₀ hC₀Z (hCs1 C₀ hC₀)
      refine ⟨S₀, hS₀, ?_⟩
      have hCs_sub : W = C₀ := by
        apply Finset.Subset.antisymm
        · rw [← hCs3]
          intro a ha
          rw [Finset.mem_sup] at ha
          rcases ha with ⟨C, hC, haC⟩
          by_cases hCC₀ : C = C₀
          · exact hCC₀ ▸ haC
          · exfalso
            have hCZ : C ⊆ Z := (Finset.le_sup (f := id) hC).trans (hCs3.le.trans hWZ)
            obtain ⟨S, hS, hCeq⟩ := hC6_only C hCZ (hCs1 C hC)
            have hdisj : Disjoint C C₀ := hCs2 hC hC₀ hCC₀
            rw [hCeq, hC₀eq, Finset.disjoint_map] at hdisj
            exact C6_not_disjoint S hS S₀ hS₀ hdisj
        · rw [← hCs3]
          exact Finset.le_sup (f := id) hC₀
      rw [hCs_sub, hC₀eq]
  let L₁ := deletion L (ground L \ (A ∪ Z))
  let L' := contraction L₁ (A \ Z)
  have hmem_L₁ : ∀ A', A' ∈ L₁ ↔ A' ∈ L ∧ A' ⊆ A ∪ Z := by
    intro A'
    simp only [L₁, deletion, Finset.mem_filter]
    refine ⟨fun ⟨hA'L, hdisj⟩ => ⟨hA'L, ?_⟩, fun ⟨hA'L, hsub⟩ => ⟨hA'L, ?_⟩⟩
    · intro a haA'
      have haG : a ∈ ground L := Finset.le_sup (f := id) hA'L haA'
      by_contra haAUZ
      exact Finset.disjoint_left.mp hdisj haA' (Finset.mem_sdiff.mpr ⟨haG, haAUZ⟩)
    · rw [Finset.disjoint_left]
      intro a haA' haG
      exact (Finset.mem_sdiff.mp haG).2 (hsub haA')
  have hsdiff_eq_inter : ∀ A' ∈ L₁, A' \ (A \ Z) = A' ∩ Z := by
    intro A' hA'
    rw [hmem_L₁] at hA'
    have hmin := hA_min A' hA'.1 hA'.2
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨haA', haAZ⟩
      refine ⟨haA', ?_⟩
      by_contra haZ
      have haA'Z : a ∈ A' \ Z := Finset.mem_sdiff.mpr ⟨haA', haZ⟩
      rw [hmin] at haA'Z
      exact haAZ (Finset.mem_sdiff.mp haA'Z)
    · rintro ⟨haA', haZ⟩
      exact ⟨haA', fun haAZ => haAZ.2 haZ⟩
  have himg_eq : L₁.image (· \ (A \ Z)) = Q6.image (fun Q => Q.map f) := by
    ext X
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨A', hA'L₁, rfl⟩
      rw [hsdiff_eq_inter A' hA'L₁]
      rw [hmem_L₁] at hA'L₁
      have hmin := hA_min A' hA'L₁.1 hA'L₁.2
      have hsymm_eq : symmDiff A' A = symmDiff (A' ∩ Z) (A ∩ Z) := by
        ext a
        simp only [Finset.mem_symmDiff, Finset.mem_inter]
        have hmin_iff := Finset.ext_iff.mp hmin a
        simp only [Finset.mem_sdiff] at hmin_iff
        by_cases haZ : a ∈ Z
        · simp [haZ]
        · have hA'A : a ∈ A' ↔ a ∈ A :=
            ⟨fun h => (hmin_iff.mp ⟨h, haZ⟩).1, fun h => (hmin_iff.mpr ⟨h, haZ⟩).1⟩
          simp [haZ, hA'A]
      have hsymm_sub : symmDiff A' A ⊆ Z := by
        rw [hsymm_eq]
        intro a ha
        rw [Finset.mem_symmDiff] at ha
        rcases ha with ⟨ha1, _⟩ | ⟨ha2, _⟩
        · exact (Finset.mem_inter.mp ha1).2
        · exact (Finset.mem_inter.mp ha2).2
      have hsymm_even : ∀ B ∈ blocker L, Even (symmDiff A' A ∩ B).card := by
        intro B hB
        have hsum := card_symmDiff_inter A' A B
        rcases hbin A' hA'L₁.1 B hB with ⟨k, hk⟩
        rcases hbin A hA B hB with ⟨m, hm⟩
        refine ⟨k + m + 1 - ((A' ∩ A) ∩ B).card, ?_⟩
        omega
      have hX_recover : A' ∩ Z = symmDiff (A ∩ Z) (symmDiff (A' ∩ Z) (A ∩ Z)) := by
        rw [symmDiff_comm (A' ∩ Z), symmDiff_symmDiff_cancel_left]
      rcases hcycle_sub_Z (symmDiff A' A) hsymm_sub hsymm_even with hemp | ⟨S, hS, hSeq⟩
      · refine ⟨A0, A0_mem_Q6, ?_⟩
        rw [hX_recover, ← hsymm_eq, hemp]
        change A0.map f = symmDiff (A ∩ Z) ⊥
        rw [symmDiff_bot, hAZ]
      · refine ⟨symmDiff A0 S, C6_symmDiff_mem_Q6 S hS, ?_⟩
        rw [hX_recover, ← hsymm_eq, hSeq, hAZ, finset_map_symmDiff]
    · rintro ⟨Q, hQ, rfl⟩
      rcases Q6_cases Q hQ with rfl | ⟨S, hS, rfl⟩
      · refine ⟨A, (hmem_L₁ A).mpr ⟨hA, Finset.subset_union_left⟩, ?_⟩
        rw [hsdiff_eq_inter A ((hmem_L₁ A).mpr ⟨hA, Finset.subset_union_left⟩), hAZ]
      · let C := S.map f
        have hCcirc : IsCircuit L C := hC6_circ S hS
        have hCZ : C ⊆ Z := by
          rw [hZ_map]
          exact Finset.map_subset_map.mpr (Finset.subset_univ S)
        let W := symmDiff A C
        have hWAUZ : W ⊆ A ∪ Z := by
          intro a ha
          rw [Finset.mem_symmDiff] at ha
          rcases ha with ⟨haA, _⟩ | ⟨haC, _⟩
          · exact Finset.mem_union_left _ haA
          · exact Finset.mem_union_right _ (hCZ haC)
        have hWG : W ⊆ ground L := by
          intro a ha
          rcases Finset.mem_union.mp (hWAUZ ha) with haA | haZ'
          · exact Finset.le_sup (f := id) hA haA
          · exact hZ haZ'
        have hWodd : ∀ B ∈ blocker L, Odd (W ∩ B).card := by
          intro B hB
          dsimp only [W]
          have hsum := card_symmDiff_inter A C B
          rcases hbin A hA B hB with ⟨k, hk⟩
          rcases hCcirc.2.1.2 B hB with ⟨m, hm⟩
          refine ⟨k + m - ((A ∩ C) ∩ B).card, ?_⟩
          omega
        have hWZ_inter : W ∩ Z = (symmDiff A0 S).map f := by
          rw [← finset_map_symmDiff, ← hAZ]
          change symmDiff A C ∩ Z = symmDiff (A ∩ Z) C
          ext a
          simp only [Finset.mem_inter, Finset.mem_symmDiff]
          by_cases haZ : a ∈ Z
          · simp [haZ]
          · have haC : a ∉ C := fun h => haZ (hCZ h)
            simp [haZ, haC]
        have hWZ_sdiff : W \ Z = A \ Z := by
          change symmDiff A C \ Z = A \ Z
          ext a
          simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
          by_cases haZ : a ∈ Z
          · simp [haZ]
          · have haC : a ∉ C := fun h => haZ (hCZ h)
            simp [haZ, haC]
        obtain ⟨A', hA'L, Cs, _, _, _, hA'Cs⟩ :=
          (parity_decomposition L hL hbin W hWG).2 hWodd
        have hA'W : A' ⊆ W := by
          rw [← hA'Cs]
          exact Finset.subset_union_left
        have hA'AUZ : A' ⊆ A ∪ Z := hA'W.trans hWAUZ
        have hA'Z_sdiff : A' \ Z = W \ Z := by
          rw [hA_min A' hA'L hA'AUZ, hWZ_sdiff]
        have hsymm_WA' : symmDiff W A' ⊆ W ∩ Z := by
          intro a ha
          rw [Finset.mem_symmDiff] at ha
          rcases ha with ⟨haW, haA'⟩ | ⟨haA', haW⟩
          · refine Finset.mem_inter.mpr ⟨haW, ?_⟩
            by_contra haZ
            have haWZ : a ∈ W \ Z := Finset.mem_sdiff.mpr ⟨haW, haZ⟩
            rw [← hA'Z_sdiff] at haWZ
            exact haA' (Finset.mem_sdiff.mp haWZ).1
          · exact False.elim (haW (hA'W haA'))
        have hsymm_Z : symmDiff W A' ⊆ Z := hsymm_WA'.trans Finset.inter_subset_right
        have hsymm_even : ∀ B ∈ blocker L, Even (symmDiff W A' ∩ B).card := by
          intro B hB
          have hsum := card_symmDiff_inter W A' B
          rcases hWodd B hB with ⟨k, hk⟩
          rcases hbin A' hA'L B hB with ⟨m, hm⟩
          refine ⟨k + m + 1 - ((W ∩ A') ∩ B).card, ?_⟩
          omega
        have hWA'_eq : A' = W := by
          rcases hcycle_sub_Z (symmDiff W A') hsymm_Z hsymm_even with hemp | ⟨S', hS', hS'eq⟩
          · apply Finset.Subset.antisymm hA'W
            intro a haW
            by_contra haA'
            have ha_mem : a ∈ symmDiff W A' :=
              Finset.mem_symmDiff.mpr (Or.inl ⟨haW, haA'⟩)
            rw [hemp] at ha_mem
            exact Finset.notMem_empty a ha_mem
          · exfalso
            have hle := Finset.card_le_card hsymm_WA'
            rw [hS'eq, Finset.card_map, C6_card S' hS', hWZ_inter, Finset.card_map,
              Q6_card (symmDiff A0 S) (C6_symmDiff_mem_Q6 S hS)] at hle
            omega
        have hA'L₁ : A' ∈ L₁ := (hmem_L₁ A').mpr ⟨hA'L, hA'AUZ⟩
        refine ⟨A', hA'L₁, ?_⟩
        rw [hsdiff_eq_inter A' hA'L₁, hWA'_eq, hWZ_inter]
  have hL'_eq : L' = Q6.image (fun Q => Q.map f) := by
    change (L₁.image (· \ (A \ Z))).filter
      (fun X => ∀ X' ∈ L₁.image (· \ (A \ Z)), X' ⊆ X → X' = X) =
        Q6.image (fun Q => Q.map f)
    rw [himg_eq, Finset.filter_true_of_mem]
    intro X hX X' hX' hsub
    rw [Finset.mem_image] at hX hX'
    rcases hX with ⟨Q, hQ, rfl⟩
    rcases hX' with ⟨Q', hQ', rfl⟩
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_map, Finset.card_map, Q6_card Q hQ, Q6_card Q' hQ']
  refine ⟨L', ?_, f, hL'_eq⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      ⟨ground L \ (A ∪ Z), Or.inl rfl⟩)
    ⟨A \ Z, Or.inr rfl⟩
