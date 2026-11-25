-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.exists_colsFixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:55:46.354916+00:00
-- url     : https://prove2.me/submissions/9c9b39c8-81ff-40c5-a3df-622cb3be240a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_col_inr_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_col_inl_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
private theorem mem_symplecticGroup_of_mem_spH (g : ℕ) :
    ∀ O ∈ spH g, O ∈ symplecticGroup (Fin g) ℤ := by
  intro O hO
  have hle : Submonoid.closure (spGens g) ≤ symplecticGroup (Fin g) ℤ := by
    rw [Submonoid.closure_le]
    intro M hM'
    rw [SetLike.mem_coe]
    rcases hM' with ((⟨S, hS, rfl⟩ | ⟨U, rfl⟩) | hJ)
    · (first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
      rw [spTransl, Matrix.J, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [hS.eq]
    · have hU2 : (U : Matrix (Fin g) (Fin g) ℤ) * (↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ) = 1 := by
        first
        | exact Units.mul_inv U
        | exact Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units U)
      have hU : ((↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ)ᵀ) * (U : Matrix (Fin g) (Fin g) ℤ)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hU2, Matrix.transpose_one]
      (first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
      rw [spDiag, Matrix.J, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [hU, hU2]
      rw [← Matrix.transpose_mul]
      first
      | rw [Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units U), Matrix.transpose_one]
      | rw [← Matrix.coe_units_inv, Units.mul_inv, Matrix.transpose_one]
    · rw [Set.mem_singleton_iff] at hJ
      rw [hJ]
      first
      | exact SymplecticGroup.J_mem
      | exact Matrix.J_mem
      | ((first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
         rw [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
           Matrix.fromBlocks_multiply]
         simp)

  exact hle hO
end ReciprocityTheory.ChartRestriction.G.Key.Chi
end

set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hM : M ∈ symplecticGroup (Fin g) ℤ) : ∀ k : ℕ, k ≤ g → ∃ O ∈ spH g, ColsFixed k (O * M) := by
  have colmul : ∀ (A N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (c : Fin g ⊕ Fin g),
      (∀ r, N r c = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r c) →
      (∀ r, A r c = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r c) →
      ∀ r, (A * N) r c = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r c := by
    intro A N c hN hA r
    rw [Matrix.mul_apply]
    simp_rw [hN]
    rw [← Matrix.mul_apply, Matrix.mul_one, hA]
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨O1, hO1, hF1⟩ := ih (by omega)
    let kk : Fin g := ⟨k, by omega⟩
    have hS1 : O1 * M ∈ symplecticGroup (Fin g) ℤ := mul_mem (mem_symplecticGroup_of_mem_spH g O1 hO1) hM
    obtain ⟨O2, hO2, hF2, h2⟩ := col_inl_step kk (O1 * M) hS1 hF1
    have hS2 : O2 * (O1 * M) ∈ symplecticGroup (Fin g) ℤ := mul_mem (mem_symplecticGroup_of_mem_spH g O2 hO2) hS1
    have hF2' : ColsFixed k (O2 * (O1 * M)) := fun i hi =>
      ⟨colmul _ _ _ (hF1 i hi).1 (hF2 i hi).1, colmul _ _ _ (hF1 i hi).2 (hF2 i hi).2⟩
    obtain ⟨O3, hO3, hF3, h3inl, h3⟩ := col_inr_step kk (O2 * (O1 * M)) hS2 hF2' h2
    refine ⟨O3 * (O2 * O1), mul_mem hO3 (mul_mem hO2 hO1), ?_⟩
    rw [show O3 * (O2 * O1) * M = O3 * (O2 * (O1 * M)) by simp only [Matrix.mul_assoc]]
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact ⟨colmul _ _ _ (hF2' i hi).1 (hF3 i hi).1, colmul _ _ _ (hF2' i hi).2 (hF3 i hi).2⟩
    · have hik : i = kk := Fin.ext hi
      rw [hik]
      exact ⟨colmul _ _ _ h2 h3inl, h3⟩
end ReciprocityTheory.ChartRestriction.G.Key.Chi
