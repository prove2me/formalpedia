-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_twistMod_cc1f7a09138b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:51.26511+00:00
-- url     : https://prove2.me/submissions/eebebdd4-8c4b-4b02-9cc8-0bf36bc0f947

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_zero_eq_one_5ef25f86ec85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_twistMod_032661586f67

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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : ℤ) (I : Chart x) : IsUnit (twistMod k x c I) :=
  IsUnit.of_mul_eq_one (twistMod k x (-c) I) (by
    rw [twistMod_mul_twistMod, add_neg_cancel, twistMod_zero_eq_one])
end GroundTheory.Heights₂.Heights.Kleiman
