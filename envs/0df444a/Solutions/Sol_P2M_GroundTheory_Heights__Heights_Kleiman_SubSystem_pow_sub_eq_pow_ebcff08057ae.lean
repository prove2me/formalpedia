-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:14.736827+00:00
-- url     : https://prove2.me/submissions/09cf5180-eb59-478f-ba6d-e0f71bd840da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_eq_mul_d7e23ae652ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_zero_eq_one_5ef25f86ec85

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
namespace SubSystem
theorem _root_.solution (Q : SubSystem k x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact twistMod_zero_eq_one I
  | succ n ih => rw [pow_succ, ← ih]; exact SubSystem.twist_sub_eq_mul _ _ I
end SubSystem
end GroundTheory.Heights₂.Heights.Kleiman
