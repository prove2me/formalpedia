-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepData_isUnit_D_53d41fd9d7c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:58.842524+00:00
-- url     : https://prove2.me/submissions/1639a792-9529-4f9c-9a4b-02fe1e7253c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_sub_ecdec4e29c5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_mul_ed3d7223ab6a


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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
variable (T : StepData k x)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace StepData
theorem _root_.solution (I : Chart x) : IsUnit (T.D.sub I) := by
  obtain ⟨i, hi⟩ := I.2.1
  have h0 : (twistSys k x 0).sub I = 1 := by
    change twistMod k x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  have hO : IsUnit ((twistSys k x (T.m - T.c₁)).sub I) :=
    IsUnit.of_mul_eq_one ((twistSys k x (-(T.m - T.c₁))).sub I) (by rw [twistSys_sub_mul, add_neg_cancel, h0])
  obtain ⟨Q', hQ'⟩ := T.M.invertible I
  rw [StepData.D, twistMul_sub]
  exact hO.mul ((IsUnit.of_mul_eq_one _ hQ').pow _)
end StepData
end GroundTheory.Heights₂.Heights.Kleiman
