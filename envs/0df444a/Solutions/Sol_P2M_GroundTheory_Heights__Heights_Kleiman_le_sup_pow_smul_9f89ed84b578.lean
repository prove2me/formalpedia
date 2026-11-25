-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_le_sup_pow_smul_9f89ed84b578
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:21:02.494984+00:00
-- url     : https://prove2.me/submissions/4b4a5dcf-47db-4580-be1d-0d25ed334ba4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_le_sup_mul_smul_ebaf2318f821

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {G F : Submodule A M} {P : Ideal A} (h : F ≤ G ⊔ P • F) (n : ℕ) :
    F ≤ G ⊔ (P ^ n) • F := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
  | succ n ih => rw [pow_succ]; exact le_sup_mul_smul ih h
end GroundTheory.Heights₂.Heights.Kleiman
