-- Prove2me | solution 1 for SimplicialIso.Mixing.eq_4_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T05:20:25.804519+00:00
-- url     : https://prove2.me/submissions/d2ad7b2d-158a-4ece-8c68-a9da977d6b9c

import Definitions.Def_SimplicialIso_Mixing_DeltaForms

set_option backward.isDefEq.respectTransparency false

open Finset SimplicialIso.Mixing
open scoped InnerProductSpace

noncomputable section

namespace SimplicialDegreeReplacement

lemma phi_psi_mul_zero (n d : ℕ) (hd : 1 ≤ d)
    (A : Fin (d + 1) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (σ : Cell n d) :
    phi A σ * psi A σ = 0 := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hnot : ¬((∀ i : Fin (k + 1), (σ.val ∩ A i.castSucc).card = 1) ∧
      (∀ i : Fin (k + 1),
        (σ.val ∩ (if (i : ℕ) = 0 then A (Fin.last (k + 1)) else A i.castSucc)).card = 1)) := by
    rintro ⟨hp, hq⟩
    have hall (i : Fin (k + 2)) : (σ.val ∩ A i).card = 1 := by
      refine Fin.lastCases ?_ (fun j => hp j) i
      simpa using hq 0
    have hdj : ((univ : Finset (Fin (k + 2))) : Set (Fin (k + 2))).PairwiseDisjoint
        (fun i => σ.val ∩ A i) := by
      intro i _ j _ hij
      exact (hA hij).mono Finset.inter_subset_right Finset.inter_subset_right
    have hsub : univ.biUnion (fun i : Fin (k + 2) => σ.val ∩ A i) ⊆ σ.val := by
      intro v hv
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_inter.mp hi).1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdj, σ.property] at hcard
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hcard
    omega
  change (if ∀ i : Fin (k + 1), (σ.val ∩ A i.castSucc).card = 1 then _ else 0) *
    (if ∀ i : Fin (k + 1),
      (σ.val ∩ (if (i : ℕ) = 0 then A (Fin.last (k + 1)) else A i.castSucc)).card = 1
      then _ else 0) = 0
  split_ifs with hp hq
  · exact False.elim (hnot ⟨hp, hq⟩)
  · simp
  · simp
  · simp

lemma diagonal_inner_zero (n d : ℕ) (hd : 1 ≤ d)
    (A : Fin (d + 1) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (f : Cell n d → ℝ) :
    ⟪phi A, WithLp.toLp 2 (fun σ => f σ * psi A σ)⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro σ _
  change ⟪phi A σ, f σ * psi A σ⟫_ℝ = 0
  rw [RCLike.inner_apply]
  simp only [starRingEnd_apply, star_trivial]
  have h := phi_psi_mul_zero n d hd A hA σ
  calc
    _ = f σ * (phi A σ * psi A σ) := by ring
    _ = 0 := by rw [h, mul_zero]

end SimplicialDegreeReplacement

theorem solution (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d)
    (A : Fin (d + 1) → Finset (Fin n)) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (α : ℝ) :
    ⟪phi A, (degOp X - upLap X) (psi A)⟫_ℝ =
      ⟪phi A, (α • LinearMap.id - upLap X : Form n d →ₗ[ℝ] Form n d) (psi A)⟫_ℝ := by
  have hdeg : ⟪phi A, degOp X (psi A)⟫_ℝ = 0 :=
    SimplicialDegreeReplacement.diagonal_inner_zero n d hd A hA (fun σ => (deg X σ.val : ℝ))
  have hinner : ⟪phi A, psi A⟫_ℝ = 0 := by
    simpa using SimplicialDegreeReplacement.diagonal_inner_zero n d hd A hA (fun _ => 1)
  change ⟪phi A, degOp X (psi A) - upLap X (psi A)⟫_ℝ =
    ⟪phi A, α • psi A - upLap X (psi A)⟫_ℝ
  rw [inner_sub_right, inner_sub_right, inner_smul_right, hdeg, hinner]
  simp

#print axioms solution
