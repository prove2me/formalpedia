-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.C.isSymm_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:27.841345+00:00
-- url     : https://prove2.me/submissions/34562c01-43a1-4614-94a6-e85cad982f6c

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MapOfRealMul
import Theorems.Thm_PositivityTheory_ThKR_Mp_C_blocks_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.C
namespace PositivityTheory.ThKR.Mp.C
theorem _root_.solution (s : Sp l) (hd : s.1.toBlocks₁₁.det ≠ 0) :
    (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂).IsSymm := by
  have hAB : s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ = s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ := by
    have h := SymplecticGroup.mem_iff.1 s.2
    rw [← fromBlocks_toBlocks s.1] at h
    exact blocks_symm h
  have hu : IsUnit s.1.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  have hut : IsUnit s.1.toBlocks₁₁ᵀ.det := by rw [det_transpose]; exact hu
  show (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂)ᵀ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂
  rw [transpose_mul, transpose_nonsing_inv]
  calc s.1.toBlocks₁₂ᵀ * (s.1.toBlocks₁₁ᵀ)⁻¹
      = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by rw [hAB]
    _ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hut, Matrix.mul_one]
end PositivityTheory.ThKR.Mp.C
