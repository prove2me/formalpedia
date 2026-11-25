-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_neg_02d1831fe01a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:07.1738+00:00
-- url     : https://prove2.me/submissions/892cc15a-1f87-4208-ba1c-64e0bcaba2fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinkowskiBox

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
open Matrix MeasureTheory
open GroundTheory.Heights₂.Heights.PSymplMinkowskiBox
namespace GroundTheory.Heights₂.Heights.PSymplMinkowskiBox
theorem _root_.solution {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, |(A *ᵥ x) i| < a i) : ∀ i, |(A *ᵥ (-x)) i| < a i := by
  intro i
  rw [mulVec_neg, Pi.neg_apply, abs_neg]
  exact hx i
end GroundTheory.Heights₂.Heights.PSymplMinkowskiBox
