-- Prove2me | solution 1 for VanderbeiLP.Networks.konig_theorem
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:01:40.623863+00:00
-- url     : https://prove2.me/submissions/97bf6c61-38d6-4e31-8a25-66c3b67d845f

/-
König's theorem on regular bipartite graphs (Vanderbei, Theorem 14.3): if n girls and n boys each
know exactly k > 0 of the other side, symmetrically, they can be paired off with every pair
acquainted.

Hall's condition holds because the k|S| acquaintance pairs leaving a set S of girls land on the
neighbourhood N(S), where each boy accounts for at most k of them. Hall's theorem gives an
injective choice of acquaintances, which is a bijection on the finite set Fin n.
-/
import Mathlib

set_option autoImplicit false

open Finset

theorem solution (n k : ℕ) (hk : 0 < k) (knows : Fin n → Fin n → Prop)
    [DecidableRel knows]
    (hgirl : ∀ i : Fin n, (Finset.univ.filter (fun j => knows i j)).card = k)
    (hboy : ∀ j : Fin n, (Finset.univ.filter (fun i => knows i j)).card = k) :
    ∃ σ : Fin n ≃ Fin n, ∀ i : Fin n, knows i (σ i) := by
  classical
  -- Hall's condition by double counting the pairs `(i, j)` with `i ∈ s` and `knows i j`
  have hall : ∀ s : Finset (Fin n),
      s.card ≤ (s.biUnion fun i => Finset.univ.filter (fun j => knows i j)).card := by
    intro s
    set N := s.biUnion fun i => Finset.univ.filter (fun j => knows i j) with hN
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := s) (t := (Finset.univ : Finset (Fin n))) (fun i j => knows i j)
    have hL : ∑ i ∈ s, ((Finset.univ : Finset (Fin n)).bipartiteAbove (fun i j => knows i j) i).card
        = s.card * k := by
      have : ∀ i ∈ s, ((Finset.univ : Finset (Fin n)).bipartiteAbove (fun i j => knows i j) i).card
          = k := fun i _ => by simpa [Finset.bipartiteAbove] using hgirl i
      rw [Finset.sum_congr rfl this]
      simp
    have hR : ∑ j ∈ (Finset.univ : Finset (Fin n)),
        (s.bipartiteBelow (fun i j => knows i j) j).card ≤ N.card * k := by
      have hsub : ∑ j ∈ N, (s.bipartiteBelow (fun i j => knows i j) j).card
          = ∑ j ∈ (Finset.univ : Finset (Fin n)),
            (s.bipartiteBelow (fun i j => knows i j) j).card := by
        apply Finset.sum_subset (Finset.subset_univ N)
        intro j _ hjN
        rw [Finset.card_eq_zero, Finset.bipartiteBelow, Finset.filter_eq_empty_iff]
        intro i hi hij
        exact hjN (Finset.mem_biUnion.mpr ⟨i, hi, by simpa using hij⟩)
      rw [← hsub]
      calc ∑ j ∈ N, (s.bipartiteBelow (fun i j => knows i j) j).card ≤ ∑ _j ∈ N, k := by
            apply Finset.sum_le_sum
            intro j _
            calc (s.bipartiteBelow (fun i j => knows i j) j).card
                ≤ (Finset.univ.filter (fun i => knows i j)).card := by
                  apply Finset.card_le_card
                  intro i hi
                  simp only [Finset.bipartiteBelow, Finset.mem_filter] at hi ⊢
                  exact ⟨Finset.mem_univ _, hi.2⟩
              _ = k := hboy j
        _ = N.card * k := by simp
    have : s.card * k ≤ N.card * k := by omega
    exact Nat.le_of_mul_le_mul_right this hk
  obtain ⟨f, hf, hfk⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun i : Fin n => Finset.univ.filter (fun j => knows i j))).mp hall
  have hbij : Function.Bijective f := (Finite.injective_iff_bijective).mp hf
  exact ⟨Equiv.ofBijective f hbij, fun i => by simpa using hfk i⟩
