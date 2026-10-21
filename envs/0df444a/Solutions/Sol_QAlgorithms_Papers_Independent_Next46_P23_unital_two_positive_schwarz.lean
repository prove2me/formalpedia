-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.unital_two_positive_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:29:54.255688+00:00
-- url     : https://prove2.me/submissions/14236d12-b14a-49e7-bd0a-6434ff2da649

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def g64c_e (I : Type) : I ⊕ I ≃ Fin 2 × I where
  toFun x := Sum.elim (fun i => ((0:Fin 2), i)) (fun i => ((1 : Fin 2), i)) x
  invFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  left_inv x := by cases x <;> simp
  right_inv p := by
    obtain ⟨a, i⟩ := p
    fin_cases a <;> simp

theorem solution [Nonempty I] [Nonempty J] (Phi : Mat I →ₗ[ℂ] Mat J)
    (hunital : Phi 1 = 1) (hpositive : RectangularKPositive 2 Phi) : Schwarz Phi := by
  intro A
  haveI : Invertible (1 : Mat I) := invertibleOne
  haveI : Invertible (1 : Mat J) := invertibleOne
  set M0 : Matrix (I ⊕ I) (I ⊕ I) ℂ := Matrix.fromBlocks 1 A Aᴴ (Aᴴ * A) with hM0def
  have hM0 : M0.PosSemidef := by
    rw [hM0def, Matrix.PosDef.fromBlocks₁₁ _ _ Matrix.PosDef.one]
    simpa using (Matrix.PosSemidef.zero : (0 : Mat I).PosSemidef)
  set M : Mat (Fin 2 × I) := M0.submatrix (g64c_e I).symm (g64c_e I).symm with hMdef
  have hM : M.PosSemidef := hM0.submatrix _
  have hN := hpositive M hM
  have hNe : (QAlgorithms.idTensorSuperop (⇑Phi) M).submatrix (g64c_e J) (g64c_e J) =
      Matrix.fromBlocks (Phi 1) (Phi A) (Phi Aᴴ) (Phi (Aᴴ*A)) := by
    have b00 : (Matrix.of fun i i' => M ((0 : Fin 2), i) ((0 : Fin 2), i')) = 1 := by
      ext i j; simp [hMdef, hM0def, g64c_e]
    have b01 : (Matrix.of fun i i' => M ((0 : Fin 2), i) ((1 : Fin 2), i')) = A := by
      ext i j; simp [hMdef, hM0def, g64c_e]
    have b10 : (Matrix.of fun i i' => M ((1 : Fin 2), i) ((0 : Fin 2), i')) = Aᴴ := by
      ext i j; simp [hMdef, hM0def, g64c_e]
    have b11 : (Matrix.of fun i i' => M ((1 : Fin 2), i) ((1 : Fin 2), i')) = Aᴴ * A := by
      ext i j; simp [hMdef, hM0def, g64c_e]
    ext (x|x) (y|y) <;> simp [QAlgorithms.idTensorSuperop, g64c_e, b00, b01, b10, b11]
  have hN' := hN.submatrix (g64c_e J)
  rw [hNe, hunital] at hN'
  have hstar : Phi Aᴴ = (Phi A)ᴴ := by
    have h1 := hN'.1
    unfold Matrix.IsHermitian at h1
    rw [Matrix.fromBlocks_conjTranspose] at h1
    rw [Matrix.fromBlocks_inj] at h1
    rw [← h1.2.2.1]
  rw [hstar, Matrix.PosDef.fromBlocks₁₁ _ _ Matrix.PosDef.one] at hN'
  simpa [QAlgorithms.Papers.Independent.Dependency50.P28.LE] using hN'
