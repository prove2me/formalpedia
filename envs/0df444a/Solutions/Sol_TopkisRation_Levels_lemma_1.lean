-- Prove2me | solution 1 for TopkisRation.Levels.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:09:04.896916+00:00
-- url     : https://prove2.me/submissions/9b8fd1da-f166-4262-8ee3-468435d02ac0

import Mathlib



namespace TopkisRation.Levels

theorem lemma_1_core {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (A : Set (E × F)) (hA : Convex ℝ A) (φ : E × F → ℝ) (hφ : ConvexOn ℝ A φ)
    (hbdd : ∀ u, BddBelow (φ '' {q | q ∈ A ∧ q.1 = u})) :
    ConvexOn ℝ (Prod.fst '' A) (fun u => sInf (φ '' {q | q ∈ A ∧ q.1 = u})) := by
  refine ⟨hA.linear_image (LinearMap.fst ℝ E F), ?_⟩
  rintro x ⟨p1, hp1, rfl⟩ y ⟨p2, hp2, rfl⟩ a b ha hb hab
  simp only [smul_eq_mul]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hne1 : (φ '' {q | q ∈ A ∧ q.1 = p1.1}).Nonempty := ⟨φ p1, p1, ⟨hp1, rfl⟩, rfl⟩
  have hne2 : (φ '' {q | q ∈ A ∧ q.1 = p2.1}).Nonempty := ⟨φ p2, p2, ⟨hp2, rfl⟩, rfl⟩
  obtain ⟨_, ⟨q1, ⟨hq1A, hq1⟩, rfl⟩, hlt1⟩ :=
    exists_lt_of_csInf_lt hne1 (lt_add_of_pos_right (sInf (φ '' {q | q ∈ A ∧ q.1 = p1.1})) hε)
  obtain ⟨_, ⟨q2, ⟨hq2A, hq2⟩, rfl⟩, hlt2⟩ :=
    exists_lt_of_csInf_lt hne2 (lt_add_of_pos_right (sInf (φ '' {q | q ∈ A ∧ q.1 = p2.1})) hε)
  have hmem : a • q1 + b • q2 ∈ A := hA hq1A hq2A ha hb hab
  have hfst : (a • q1 + b • q2).1 = a • p1.1 + b • p2.1 := by simp [hq1, hq2]
  have h1 : sInf (φ '' {q | q ∈ A ∧ q.1 = a • p1.1 + b • p2.1}) ≤ φ (a • q1 + b • q2) :=
    csInf_le (hbdd _) ⟨_, ⟨hmem, hfst⟩, rfl⟩
  have h2 := hφ.2 hq1A hq2A ha hb hab
  simp only [smul_eq_mul] at h2
  have h3 : a * φ q1 ≤ a * (sInf (φ '' {q | q ∈ A ∧ q.1 = p1.1}) + ε) :=
    mul_le_mul_of_nonneg_left hlt1.le ha
  have h4 : b * φ q2 ≤ b * (sInf (φ '' {q | q ∈ A ∧ q.1 = p2.1}) + ε) :=
    mul_le_mul_of_nonneg_left hlt2.le hb
  have : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  nlinarith

end TopkisRation.Levels

open TopkisRation.Levels


theorem solution {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (A : Set (E × F)) (hA : Convex ℝ A) (φ : E × F → ℝ) (hφ : ConvexOn ℝ A φ)
    (hbdd : ∀ u, BddBelow (φ '' {q | q ∈ A ∧ q.1 = u})) :
    ConvexOn ℝ (Prod.fst '' A) (fun u => sInf (φ '' {q | q ∈ A ∧ q.1 = u})) := by
  exact lemma_1_core A hA φ hφ hbdd
