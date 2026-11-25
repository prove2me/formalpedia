-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrictToBlock_blockEmb_d48514eb86a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:12:06.76072+00:00
-- url     : https://prove2.me/submissions/4192e7ee-e6fa-454d-a167-4877b926a733

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (f N : ℕ) (τ σ : Fin f) (P : RootRing 1 N) :
    restrictToBlock f N τ (blockEmb f N σ P) =
      if σ = τ then toN N P else C (constantCoeff P) := by
  have key : (restrictToBlock f N τ).comp (blockEmb f N σ) =
      aeval (fun p : Fin 1 × Fin N => if σ = τ then X p.2 else 0) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [restrictToBlock, blockEmb]
  have := congrArg (fun φ : RootRing 1 N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ P) key
  simp only [AlgHom.comp_apply] at this
  rw [this]
  split_ifs with h
  · rfl
  · rw [show (fun _ : Fin 1 × Fin N => (0 : MvPolynomial (Fin N) ℚ)) = 0 from rfl,
      MvPolynomial.aeval_zero, MvPolynomial.algebraMap_eq]
end GroundTheory.Heights₂.Heights.RestTerms.Top
