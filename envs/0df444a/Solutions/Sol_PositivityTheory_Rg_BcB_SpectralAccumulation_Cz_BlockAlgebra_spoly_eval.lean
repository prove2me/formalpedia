-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.spoly_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:30:11.918259+00:00
-- url     : https://prove2.me/submissions/05bf9cef-331c-4e2e-b2b7-75ac553c94ba

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
theorem _root_.solution (n : ℕ) (χ : ℕ → ℂ) (h : χ n = 1) (u : ℂ) :
    (spoly n χ).eval u = ∑ k ∈ Finset.range (n + 1), u ^ k * χ k := by
  rw [spoly, eval_add, eval_finsetSum, Finset.sum_range_succ, h, mul_one, add_comm,
    ← Fin.sum_univ_eq_sum_range (fun k => u ^ k * χ k)]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
