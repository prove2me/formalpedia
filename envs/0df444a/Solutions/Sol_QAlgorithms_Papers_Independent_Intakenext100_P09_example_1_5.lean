-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P09.example_1_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:42:02.323514+00:00
-- url     : https://prove2.me/submissions/25939c55-5007-445d-9dc4-ff6e6b2edb72

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

universe u v w

open QAlgorithms.Papers.Independent.Intakenext100.P09 in
theorem solution {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ C : OpenCover G, C.sets = translatedFamily U ∧ InvariantCover G C ∧
      (∀ n : ℕ, IsOpen (coverDiagonal C n)) ∧
      (∀ (n : ℕ) (x : Fin (n + 1) → G), x ∈ coverDiagonal C n →
        ∀ g : G, (fun i => g * x i) ∈ coverDiagonal C n) ∧
      (∀ (n m : ℕ) (a : Fin (m + 1) → Fin (n + 1)) (x : Fin (n + 1) → G),
        x ∈ coverDiagonal C n → x ∘ a ∈ coverDiagonal C m) := by
  let C : OpenCover G :=
    { sets := translatedFamily U
      isOpen := by
        rintro W ⟨g, rfl⟩
        exact isOpenMap_mul_left g U hU
      covers := fun x => ⟨(fun y => x * y) '' U, ⟨x, rfl⟩, ⟨1, h1, mul_one x⟩⟩ }
  have hinv : InvariantCover G C := by
    rintro g W ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    rw [Set.image_image]
    congr 1
    funext y
    rw [smul_eq_mul, mul_assoc]
  refine ⟨C, rfl, hinv, ?_, ?_, ?_⟩
  · intro n
    have e : coverDiagonal C n = ⋃ W ∈ C.sets, ⋂ i, (fun x : Fin (n + 1) → G => x i) ⁻¹' W := by
      ext x
      simp [coverDiagonal]
    rw [e]
    exact isOpen_biUnion fun W hW =>
      isOpen_iInter_of_finite fun i => (C.isOpen W hW).preimage (continuous_apply i)
  · rintro n x ⟨W, hW, hx⟩ g
    exact ⟨(fun y => g • y) '' W, hinv g W hW, fun i => ⟨x i, hx i, rfl⟩⟩
  · rintro n m a x ⟨W, hW, hx⟩
    exact ⟨W, hW, fun i => hx (a i)⟩
