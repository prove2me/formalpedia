-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_gram_sumElim_of_orthogonal_30fcb0026ad7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:10.353828+00:00
-- url     : https://prove2.me/submissions/3761d2ff-a0ae-457c-835b-5294205ae485

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension

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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (v : ι → V) (w : κ → V) (h : ∀ i j, inner ℂ (v i) (w j) = 0) :
    det (gram ℂ (Sum.elim v w)) = det (gram ℂ v) * det (gram ℂ w) := by
  have hg : gram ℂ (Sum.elim v w) = fromBlocks (gram ℂ v) 0 0 (gram ℂ w) := by
    ext (i | i) (j | j)
    · simp [gram_apply]
    · simp [gram_apply, h]
    · simp [gram_apply, inner_eq_zero_symm.mp (h j i)]
    · simp [gram_apply]
  rw [hg, det_fromBlocks_zero₂₁]
end GroundTheory.Heights₂.Heights
