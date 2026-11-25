-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.apply_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:29:48.63588+00:00
-- url     : https://prove2.me/submissions/61c312a4-4144-4d6f-a4fc-35ff1c7a1df3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PBlocksAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
theorem _root_.solution (n : ℕ) (a : ℕ → Module.End ℂ M) (χ : ℕ → ℂ) (y : M)
    (hy : ∀ k ∈ Finset.range (n + 1), a k y = χ k • y) (u : ℂ) :
    (∑ k ∈ Finset.range (n + 1), u ^ k • a k) y = (∑ k ∈ Finset.range (n + 1), u ^ k * χ k) • y := by
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [LinearMap.smul_apply, hy k hk, smul_smul]
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
