-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.closure_spGens_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:38.560925+00:00
-- url     : https://prove2.me/submissions/a845278f-11a8-4aae-bfa7-11d372296e88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (g : ℕ) :
    Submonoid.closure (spGens g) = symplecticGroup (Fin g) ℤ := by
  refine le_antisymm ?_ (fun M hM => spGen g M hM)
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
end ReciprocityTheory.ChartRestriction.G.Key.Chi
