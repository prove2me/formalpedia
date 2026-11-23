-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.blocks_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:21.229122+00:00
-- url     : https://prove2.me/submissions/1f3b64df-2977-4c14-9e0e-29dbc2eb47a0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_InversionStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {g : ℕ} (M N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ ∧
    (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ ∧
    (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ ∧
    (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  have h := fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
    N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂
  rw [fromBlocks_toBlocks, fromBlocks_toBlocks] at h
  rw [h]
  simp
end ReciprocityTheory.ChartRestriction.G.Key.Chi
