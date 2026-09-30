-- Prove2me | solution 1 for UnderstandingML.birkhoff_von_neumann
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T06:40:53.205697+00:00
-- url     : https://prove2.me/submissions/4a4b7537-ce1a-44b4-9f61-e92e83f43c94

import Definitions.Def_UnderstandingML_Multiclass

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution (r : ℕ) :
    doublyStochastic ℝ (Fin r) = convexHull ℝ
      {M : Matrix (Fin r) (Fin r) ℝ | ∃ σ : Equiv.Perm (Fin r), M = σ.permMatrix ℝ} := by
  rw [doublyStochastic_eq_convexHull_permMatrix]
  congr 1
  ext M
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun ⟨σ, h⟩ => ⟨σ, h.symm⟩, fun ⟨σ, h⟩ => ⟨σ, h.symm⟩⟩
