-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.nondegeneracy_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:25:57.20945+00:00
-- url     : https://prove2.me/submissions/97be6caa-c608-4a62-be3b-503b651b209f

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06
noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Lemma 6.2, PDF p.15: all three equivalent nondegeneracy conditions,
with the nonempty requirements explicit. -/
theorem g61c_repG_bounded (rho : F → X →L[ℂ] X) (S : Set F) :
    S ⊆ boundedElements (representationGraphs rho) := fun e _ => ⟨rho e, rfl⟩


theorem solution [CompleteSpace X] (rho : F → X →L[ℂ] X) (E : Set F)
    (hrho : AlgebraRepresentationOn rho E) :
    (AnchorSet (representationGraphs rho) E ↔ Anchored (representationGraphs rho) E 1) ∧
    (AnchorSet (representationGraphs rho) E ↔ E.Nonempty ∧ (maximalAnchored rho E).Nonempty) := by
  have hmul := hrho.1.2.1
  have h1 : symbolBracket E 1 = E := by ext e; simp [symbolBracket]
  refine ⟨by simp [Anchored, h1], ?_⟩
  constructor
  · intro h
    refine ⟨h.1, 1, fun e he => ?_⟩
    have : symbolBracket E (e * 1) = E := by
      ext e'; simp only [symbolBracket, mul_one, Set.mem_setOf_eq]
      exact ⟨fun h => h.1, fun h' => ⟨h', (hmul e' h' e he).2⟩⟩
    rw [this]; exact h
  · rintro ⟨⟨e0, he0⟩, f, hf⟩
    have h := hf e0 he0
    refine ⟨⟨e0, he0⟩, g61c_repG_bounded rho E, fun x hx => h.2.2 x fun e he => hx e he.1⟩



end

