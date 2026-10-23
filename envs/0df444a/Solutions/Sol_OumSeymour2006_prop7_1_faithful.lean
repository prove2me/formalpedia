-- Prove2me | solution 1 for OumSeymour2006.prop7_1_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:30:15.255626+00:00
-- url     : https://prove2.me/submissions/9f8d1def-609d-463c-8a13-1959d1622512

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation

open ApproxCliqueWidth.Certificate Finset

namespace OS85

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem r_union_le {r : Finset V → ℤ} (hr : IsMatroidRankOn Finset.univ r) (Z T : Finset V) :
    r (Z ∪ T) ≤ r Z + (T.card : ℤ) := by
  have h1 := hr.2.2 Z T (subset_univ _) (subset_univ _)
  have h2 := (hr.1 (Z ∩ T) (subset_univ _)).1
  have h3 := (hr.1 T (subset_univ _)).2
  linarith

/-- `φ(X,Y) = r(X ∪ (B \ Y)) - |B \ Y|` -/
def φ (r : Finset V → ℤ) (B X Y : Finset V) : ℤ := r (X ∪ (B \ Y)) - ((B \ Y).card : ℤ)

theorem φ_mono {r : Finset V → ℤ} (hr : IsMatroidRankOn Finset.univ r) (B : Finset V)
    {X X' Y Y' : Finset V} (hX : X ⊆ X') (hY : Y ⊆ Y') : φ r B X Y ≤ φ r B X' Y' := by
  unfold φ
  set T := (B \ Y) \ (B \ Y')
  have hsplit : B \ Y = (B \ Y') ∪ T := by
    ext x; simp only [T, mem_union, mem_sdiff]; constructor
    · intro h; by_cases hx : x ∈ Y' <;> tauto
    · rintro (h | h)
      · exact ⟨h.1, fun hy => h.2 (hY hy)⟩
      · exact h.1
  have hdis : Disjoint (B \ Y') T := by
    rw [disjoint_left]; intro x h1 h2; exact (mem_sdiff.mp h2).2 h1
  have hc : ((B \ Y).card : ℤ) = ((B \ Y').card : ℤ) + (T.card : ℤ) := by
    rw [hsplit, card_union_of_disjoint hdis]; push_cast; ring
  have h1 : r (X ∪ (B \ Y)) ≤ r (X' ∪ (B \ Y')) + (T.card : ℤ) := by
    rw [hsplit, ← union_assoc]
    refine (r_union_le hr _ _).trans ?_
    have := hr.2.1 (X ∪ (B \ Y')) (X' ∪ (B \ Y')) (union_subset_union_left hX) (subset_univ _)
    linarith
  linarith

theorem card_sdiff_pair (B X Y : Finset V) :
    ((B \ (X ∪ Y)).card : ℤ) + ((B \ (X ∩ Y)).card : ℤ) = ((B \ X).card : ℤ) + ((B \ Y).card : ℤ) := by
  have e1 : B \ (X ∪ Y) = (B \ X) ∩ (B \ Y) := by ext; simp; tauto
  have e2 : B \ (X ∩ Y) = (B \ X) ∪ (B \ Y) := by ext; simp; tauto
  rw [e1, e2]
  have := congrArg (fun n : ℕ => (n : ℤ)) (card_union_add_card_inter (B \ X) (B \ Y))
  push_cast at this; linarith

theorem φ_submod {r : Finset V → ℤ} (hr : IsMatroidRankOn Finset.univ r) (B A A' C C' : Finset V) :
    φ r B (A ∩ C) (A' ∪ C') + φ r B (A ∪ C) (A' ∩ C') ≤ φ r B A A' + φ r B C C' := by
  unfold φ
  have hc := card_sdiff_pair B A' C'
  set P := A ∪ (B \ A')
  set Q := C ∪ (B \ C')
  have hs := hr.2.2 P Q (subset_univ _) (subset_univ _)
  have h1 : r ((A ∩ C) ∪ (B \ (A' ∪ C'))) ≤ r (P ∩ Q) :=
    hr.2.1 _ _ (by intro x; simp only [P, Q, mem_union, mem_inter, mem_sdiff]; tauto) (subset_univ _)
  have h2 : (A ∪ C) ∪ (B \ (A' ∩ C')) = P ∪ Q := by
    ext x; simp only [P, Q, mem_union, mem_inter, mem_sdiff]; tauto
  rw [h2]
  linarith

end OS85

open OS85 in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (r : Finset V → ℤ) (hr : IsMatroidRankOn Finset.univ r)
    (B : Finset V) (hBindep : r B = (B.card : ℤ)) (hBspan : r B = r Finset.univ) :
    IsInterpolation (fun X => r X + r Xᶜ - r Finset.univ + 1)
      (fun X Y => r (X ∪ (B \ Y)) + r (Y ∪ (B \ X))
        - ((B \ X).card : ℤ) - ((B \ Y).card : ℤ) + 1) := by
  have hφ : ∀ X Y, r (X ∪ (B \ Y)) + r (Y ∪ (B \ X)) - ((B \ X).card : ℤ) - ((B \ Y).card : ℤ) + 1
      = φ r B X Y + φ r B Y X + 1 := by intro X Y; unfold φ; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X
    have e1 : X ∪ (B \ Xᶜ) = X := by
      ext x; simp only [mem_union, mem_sdiff, mem_compl]; tauto
    have e2 : Xᶜ ∪ (B \ X) = Xᶜ := by
      ext x; simp only [mem_union, mem_sdiff, mem_compl]; tauto
    have e3 : B \ Xᶜ = B ∩ X := by ext x; simp
    have hcard := card_inter_add_card_sdiff B X
    simp only
    rw [e1, e2, e3, ← hBspan, hBindep]
    push_cast [← hcard]; ring
  · intro A B' C D _ hAC hBD
    simp only
    rw [hφ, hφ]
    have := φ_mono hr B hAC hBD
    have := φ_mono hr B hBD hAC
    linarith
  · intro A B' C D _ _
    simp only
    rw [hφ, hφ, hφ, hφ]
    have h1 := φ_submod hr B A B' C D
    have h2 := φ_submod hr B B' A D C
    rw [union_comm B' D, inter_comm B' D] at *
    linarith [h1, h2, show φ r B (B' ∪ D) (A ∩ C) = φ r B (D ∪ B') (A ∩ C) by rw [union_comm],
      show φ r B (B' ∩ D) (A ∪ C) = φ r B (D ∩ B') (A ∪ C) by rw [inter_comm]]
  · simp only [compl_empty, sdiff_empty, empty_union]
    have h0 := hr.1 ∅ (subset_univ _)
    simp at h0
    have : r ∅ = 0 := by linarith [h0.1, h0.2]
    rw [this, hBindep]; ring
