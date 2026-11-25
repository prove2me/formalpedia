-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_trdeg_adjoin_eq_cRk_b84e0c0b014c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:47.944856+00:00
-- url     : https://prove2.me/submissions/b9dc87a3-cc2b-4818-a80a-6efc1a2f5f38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegAdjoinLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTrdegAdjoinLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_matroid_subalgebra_eq_comap_8672c70b9c6d

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
open Algebra Cardinal Set AlgebraicIndependent
noncomputable section
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (A : Set Ω) :
    Algebra.trdeg K (Algebra.adjoin K A) = (AlgebraicIndependent.matroid K Ω).cRk A := by
  rw [← matroid_cRank_eq, matroid_subalgebra_eq_comap, ← Matroid.cRk_ground, Matroid.comap_ground_eq,
    Matroid.cRk_comap, matroid_e, preimage_univ, image_univ, Subtype.range_coe]
  refine le_antisymm ?_ (Matroid.cRk_le_of_subset _ Algebra.subset_adjoin)
  refine (Matroid.cRk_le_of_subset _ ?_).trans_eq (Matroid.cRk_closure _ A)
  intro x hx
  rw [matroid_closure_eq]
  exact isAlgebraic_algebraMap (⟨x, hx⟩ : Algebra.adjoin K A)
end GroundTheory.Heights₂.Heights
