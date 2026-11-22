-- Prove2me | solution 1 for ShiShallow.runLayered_eq_circMatrix_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T18:29:18.343597+00:00
-- url     : https://prove2.me/submissions/1cefd19f-c51c-4e1f-9ac1-b52469e582cf

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow
open Matrix

theorem solution {n : ℕ}
    (hA : ∀ (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n),
      apply1 U i ψ = apply1Matrix U i *ᵥ ψ)
    (hC : ∀ (i j : Fin n) (hij : i ≠ j) (ψ : QState n),
      cnotState i j hij ψ = cnotMatrix i j *ᵥ ψ)
    (c : Layered n) (ψ : QState n) :
    runLayered c ψ = circMatrix c *ᵥ ψ := by
  -- gate level: the two crux bridges, dispatched over the five constructors
  have hg : ∀ (g : Instr n) (φ : QState n), g.apply φ = gateMatrix g *ᵥ φ := by
    intro g φ
    cases g with
    | h i => exact hA hMat i φ
    | s i => exact hA sMat i φ
    | t i => exact hA tMat i φ
    | x i => exact hA xMat i φ
    | cnot i j hij => exact hC i j hij φ
  -- layer level: `runLayer` is a left fold, `layerMatrix` a reversed product; they agree
  have hl : ∀ (l : List (Instr n)) (φ : QState n), runLayer l φ = layerMatrix l *ᵥ φ := by
    intro l
    induction l with
    | nil =>
        intro φ
        first
          | (show φ = (1 : Op n) *ᵥ φ
             rw [Matrix.one_mulVec]
             done)
          | (simp [runLayer, layerMatrix]; done)
    | cons g t ih =>
        intro φ
        first
          | (show runLayer t (g.apply φ) = (layerMatrix t * gateMatrix g) *ᵥ φ
             rw [ih (g.apply φ), hg g φ, Matrix.mulVec_mulVec]
             done)
          | (simp only [runLayer, layerMatrix]
             rw [ih (g.apply φ), hg g φ, Matrix.mulVec_mulVec]
             done)
  -- circuit level: same shape one layer up
  induction c generalizing ψ with
  | nil =>
      first
        | (show ψ = (1 : Op n) *ᵥ ψ
           rw [Matrix.one_mulVec]
           done)
        | (simp [runLayered, circMatrix]; done)
  | cons l t ih =>
      first
        | (show runLayered t (runLayer l ψ) = (circMatrix t * layerMatrix l) *ᵥ ψ
           rw [ih (runLayer l ψ), hl l ψ, Matrix.mulVec_mulVec]
           done)
        | (simp only [runLayered, circMatrix]
           rw [ih (runLayer l ψ), hl l ψ, Matrix.mulVec_mulVec]
           done)
