-- Prove2me | solution 1 for SubmodOrder.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:34:39.400565+00:00
-- url     : https://prove2.me/submissions/86495e5b-ad7d-4987-b410-5fdc8acc99cf

import Mathlib
import Definitions.Def_SubmodOrder_marginal
import Definitions.Def_SubmodOrder_IsWeakSubmodularOrder
import Definitions.Def_SubmodOrder_IsInterleavedPartition

set_option autoImplicit false

open SubmodOrder

theorem solution {α : Type*} [DecidableEq α] {n m : ℕ} (f : Finset α → ℝ) (π : α ≃ Fin n)
    (hπ : IsWeakSubmodularOrder f π) (O E : Fin m → Finset α) (A : Finset α)
    (hA : IsInterleavedPartition π O E A) :
    f A ≤ f (Eprefix E m) + ∑ ℓ : Fin m, marginal f (O ℓ) (Eprefix E ℓ.val) := by
  obtain ⟨hA_eq, hOE, hEO, hOO, hEE⟩ := hA
  let S : ℕ → Finset α := fun j =>
    Eprefix E j ∪ (Finset.univ.filter fun ℓ : Fin m => j ≤ ℓ.val).biUnion (fun ℓ => O ℓ ∪ E ℓ)
  have hS0 : S 0 = A := by
    ext x
    rw [hA_eq]
    simp [S, Eprefix]
  have hSm : S m = Eprefix E m := by
    ext x
    simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro (h | ⟨ℓ, hℓ, -⟩)
      · exact h
      · exfalso; have := ℓ.isLt; omega
    · exact Or.inl
  have hstep : ∀ k : Fin m,
      f (S k.val) - f (S (k.val + 1)) ≤ marginal f (O k) (Eprefix E k.val) := by
    intro k
    let R : Finset α :=
      E k ∪ (Finset.univ.filter fun ℓ : Fin m => k.val + 1 ≤ ℓ.val).biUnion (fun ℓ => O ℓ ∪ E ℓ)
    have hSk : S k.val = R ∪ (O k ∪ Eprefix E k.val) := by
      ext x
      simp only [S, R, Eprefix, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (⟨i, hi, hxE⟩ | ⟨ℓ, hℓ, hxOE⟩)
        · exact Or.inr (Or.inr ⟨i, hi, hxE⟩)
        · by_cases hℓk : ℓ = k
          · subst hℓk
            rcases hxOE with hxO | hxE
            · exact Or.inr (Or.inl hxO)
            · exact Or.inl (Or.inl hxE)
          · have hlt : k.val + 1 ≤ ℓ.val := by
              have : ℓ.val ≠ k.val := fun h => hℓk (Fin.ext h)
              omega
            exact Or.inl (Or.inr ⟨ℓ, hlt, hxOE⟩)
      · rintro ((hxEk | ⟨ℓ, hℓ, hxOE⟩) | (hxOk | ⟨i, hi, hxEi⟩))
        · exact Or.inr ⟨k, le_rfl, Or.inr hxEk⟩
        · exact Or.inr ⟨ℓ, by omega, hxOE⟩
        · exact Or.inr ⟨k, le_rfl, Or.inl hxOk⟩
        · exact Or.inl ⟨i, hi, hxEi⟩
    have hSk1 : S (k.val + 1) = R ∪ Eprefix E k.val := by
      ext x
      simp only [S, R, Eprefix, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (⟨i, hi, hxEi⟩ | ⟨ℓ, hℓ, hxOE⟩)
        · by_cases hik : i = k
          · subst hik; exact Or.inl (Or.inl hxEi)
          · have : i.val ≠ k.val := fun h => hik (Fin.ext h)
            exact Or.inr ⟨i, by omega, hxEi⟩
        · exact Or.inl (Or.inr ⟨ℓ, hℓ, hxOE⟩)
      · rintro ((hxEk | ⟨ℓ, hℓ, hxOE⟩) | ⟨i, hi, hxEi⟩)
        · exact Or.inl ⟨k, Nat.lt_succ_self _, hxEk⟩
        · exact Or.inr ⟨ℓ, hℓ, hxOE⟩
        · exact Or.inl ⟨i, by omega, hxEi⟩
    have hnest : IsPiNested π (Eprefix E k.val) (O k ∪ Eprefix E k.val) := by
      refine ⟨Finset.subset_union_right, ?_⟩
      intro b hb a ha
      obtain ⟨hx_union, hx_not⟩ := Finset.mem_sdiff.mp ha
      have haO : a ∈ O k := (Finset.mem_union.mp hx_union).resolve_right hx_not
      simp only [Eprefix, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      obtain ⟨i, hi, hbEi⟩ := hb
      exact hEO i k hi b hbEi a haO
    have hright : IsRightOf π (O k ∪ Eprefix E k.val) R := by
      intro a ha c hc
      rcases Finset.mem_union.mp ha with haO | haE
      · simp only [R, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
          true_and] at hc
        rcases hc with hcEk | ⟨ℓ, hℓ, hcOE⟩
        · exact hOE k k le_rfl a haO c hcEk
        · have hkℓ : k < ℓ := by change k.val < ℓ.val; omega
          rcases hcOE with hcO | hcE
          · exact hOO k ℓ hkℓ a haO c hcO
          · exact hOE k ℓ hkℓ.le a haO c hcE
      · simp only [Eprefix, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at haE
        obtain ⟨i, hi, haEi⟩ := haE
        have hik : i < k := hi
        simp only [R, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
          true_and] at hc
        rcases hc with hcEk | ⟨ℓ, hℓ, hcOE⟩
        · exact hEE i k hik a haEi c hcEk
        · have hiℓ : i < ℓ := by change i.val < ℓ.val; omega
          rcases hcOE with hcO | hcE
          · exact hEO i ℓ hiℓ a haEi c hcO
          · exact hEE i ℓ hiℓ a haEi c hcE
    have hsubmod := hπ (O k ∪ Eprefix E k.val) (Eprefix E k.val) R hnest hright
    unfold marginal at hsubmod ⊢
    rw [hSk, hSk1]
    linarith
  have htele : ∀ j, j ≤ m →
      f (S 0) - f (S j) ≤
        ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin m => ℓ.val < j),
          marginal f (O ℓ) (Eprefix E ℓ.val) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hjm
      let k : Fin m := ⟨j, hjm⟩
      have h1 := ih (by omega)
      have h2 := hstep k
      have hfilt : Finset.univ.filter (fun ℓ : Fin m => ℓ.val < j + 1) =
          insert k (Finset.univ.filter (fun ℓ : Fin m => ℓ.val < j)) := by
        ext ℓ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro h
          by_cases heq : ℓ.val = j
          · exact Or.inl (Fin.ext heq)
          · exact Or.inr (by omega)
        · rintro (rfl | h)
          · exact Nat.lt_succ_self j
          · omega
      have hnotmem : k ∉ Finset.univ.filter (fun ℓ : Fin m => ℓ.val < j) := by
        simp [k]
      rw [hfilt, Finset.sum_insert hnotmem]
      change f (S 0) - f (S (j + 1)) ≤
        marginal f (O k) (Eprefix E j) +
          ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin m => ℓ.val < j),
            marginal f (O ℓ) (Eprefix E ℓ.val)
      change f (S j) - f (S (j + 1)) ≤ marginal f (O k) (Eprefix E j) at h2
      linarith
  have hfin := htele m le_rfl
  have huniv : Finset.univ.filter (fun ℓ : Fin m => ℓ.val < m) = Finset.univ :=
    Finset.filter_true_of_mem fun ℓ _ => ℓ.isLt
  rw [hS0, hSm, huniv] at hfin
  linarith
