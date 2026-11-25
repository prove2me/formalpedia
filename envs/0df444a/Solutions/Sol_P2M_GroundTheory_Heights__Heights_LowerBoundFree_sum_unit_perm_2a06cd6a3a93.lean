-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_sum_unit_perm_2a06cd6a3a93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:29.171007+00:00
-- url     : https://prove2.me/submissions/5384f4ed-d955-473a-abf5-fc153ffef9a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_perm_fin_two_univ_830315b3909e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {M : Type*} [AddCommMonoid M] (g : (Unit → Equiv.Perm (Fin 2)) → M) :
    ∑ w, g w = g (fun _ => 1) + g (fun _ => Equiv.swap 0 1) := by
  rw [← (Equiv.funUnique Unit (Equiv.Perm (Fin 2))).symm.sum_comp, perm_fin_two_univ,
    Finset.sum_pair (by decide)]
  rfl
end GroundTheory.Heights₂.Heights.LowerBoundFree
