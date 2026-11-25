-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_le_ker_add408c5818c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:35.755809+00:00
-- url     : https://prove2.me/submissions/a73a37ca-44df-4dcf-bbf7-31408f965a9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_rabinowitschEval_rename_ff6a73805728

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
open MvPolynomial
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    rabinowitschIdeal K g ≤ RingHom.ker (rabinowitschEval K g) := by
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    simp [RingHom.mem_ker, rabinowitschEval_rename, Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_one, rabinowitschEval_rename]
    rw [show rabinowitschEval K g (X none) = IsLocalization.Away.invSelf (Ideal.Quotient.mk K g) by
      simp [rabinowitschEval], mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
end GroundTheory.Heights₂.Heights
