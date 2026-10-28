-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.count_bounds_and_residue_offsets
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:53:10.252974+00:00
-- url     : https://prove2.me/submissions/7c418bcb-901e-4192-abcf-1196329bc43f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_complete_residue_count_classification

noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

lemma X4P10R_offsets (i : Fin 26) :
    -1 ≤ (figureVertices i).tOffset ∧ (figureVertices i).tOffset ≤ 3 ∧
    0 ≤ (figureVertices i).hOffset ∧ (figureVertices i).hOffset ≤ 2 := by
  fin_cases i <;> simp [figureVertices]

/-- Corollary 7.11, PDF p.11, reduced to Theorem 7.10. -/
theorem solution (M : ModifiedForm) :
    let k := complexLde (modifiedValue M)
    let t := modifiedTCount M
    let h := modifiedHCount M
    (2 * (k : ℤ) - 3 ≤ (t : ℤ) ∧ (t : ℤ) ≤ 2 * (k : ℤ) + 1) ∧
    (2 * (k : ℤ) - 2 ≤ (h : ℤ) ∧ (h : ℤ) ≤ 2 * (k : ℤ)) ∧
    ∀ N : ModifiedForm,
      matrixResidue (modifiedValue N) (complexLde (modifiedValue N)) =
        matrixResidue (modifiedValue M) k →
      2 * (complexLde (modifiedValue N) : ℤ) - (modifiedTCount N : ℤ) =
        2 * (k : ℤ) - (t : ℤ) ∧
      2 * (complexLde (modifiedValue N) : ℤ) - (modifiedHCount N : ℤ) =
        2 * (k : ℤ) - (h : ℤ) := by
  intro k t h
  obtain ⟨i, hi, huniq, ht, hh, -, -⟩ := complete_residue_count_classification M
  obtain ⟨o1, o2, o3, o4⟩ := X4P10R_offsets i
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
  intro N hN
  obtain ⟨j, hj, -, ht', hh', -, -⟩ := complete_residue_count_classification N
  have hji : j = i := huniq j (by rw [← hN]; exact hj)
  subst hji
  exact ⟨by rw [ht', ht], by rw [hh', hh]⟩

end
