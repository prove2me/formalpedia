-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_prod_mem_pow_64615a997730
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:15.590667+00:00
-- url     : https://prove2.me/submissions/0358342d-e516-4fd7-809a-0626966e6f86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9


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
open Filter
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
theorem _root_.solution {r : ℕ} (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ H.secs)
    (I : Chart x) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.card_empty]; exact one_mem_twistMod_zero I
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    have h1 : h a ∈ (H.pow 1).sub I := by
      rw [SubSystem.pow_sub, pow_one]
      exact (Submodule.restrictScalars_mem _ _ _).mp ((Submodule.mem_iInf _).mp (hh a) I)
    exact AmpleTwistLocal.mul_mem_pow H I ih 1 h1
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
