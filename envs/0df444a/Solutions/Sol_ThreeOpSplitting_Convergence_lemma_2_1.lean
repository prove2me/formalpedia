-- Prove2me | solution 1 for ThreeOpSplitting.Convergence.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:45:04.310518+00:00
-- url     : https://prove2.me/submissions/d3e5f795-fae3-4e49-bd35-3761c21a3385

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration



namespace ThreeOpSplitting.Convergence

theorem lemma_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ : ℝ) (JA JB : H → H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ : 0 < γ)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB) (z : H) :
    let xB := JB z
    let z' := (2 : ℝ) • xB - z
    let z'' := z' - γ • C xB
    let xA := JA z''
    let uB := γ⁻¹ • (z - xB)
    let uA := γ⁻¹ • (z'' - xA)
    uB ∈ B xB ∧ uA ∈ A xA ∧
      threeOp γ JA JB C z - z = xA - xB ∧
      xA - xB = -(γ • (uB + uA + C xB)) ∧
      threeOp γ JA JB C z = xA + γ • uB := by
  intro xB z' z'' xA uB uA
  have hg : γ ≠ 0 := hγ.ne'
  refine ⟨hJB z, hJA z'', ?_, ?_, ?_⟩
  · simp only [threeOp, xA, z'', z', xB]; abel
  · simp only [uB, uA, smul_add, smul_smul, mul_inv_cancel₀ hg, one_smul, z'', z']
    module
  · simp only [threeOp, xA, z'', z', xB, uB, smul_smul, mul_inv_cancel₀ hg, one_smul]
    abel

end ThreeOpSplitting.Convergence

open ThreeOpSplitting.Convergence

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ : ℝ) (JA JB : H → H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ : 0 < γ)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB) (z : H) :
    let xB := JB z
    let z' := (2 : ℝ) • xB - z
    let z'' := z' - γ • C xB
    let xA := JA z''
    let uB := γ⁻¹ • (z - xB)
    let uA := γ⁻¹ • (z'' - xA)
    uB ∈ B xB ∧ uA ∈ A xA ∧
      threeOp γ JA JB C z - z = xA - xB ∧
      xA - xB = -(γ • (uB + uA + C xB)) ∧
      threeOp γ JA JB C z = xA + γ • uB := by
  exact lemma_2_1 A B C β γ JA JB hA hB hβ hC hγ hJA hJB z
