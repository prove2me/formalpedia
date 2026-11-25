-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_prod_pow_mem_3b44bad7dd98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:30:49.231336+00:00
-- url     : https://prove2.me/submissions/0ce90c28-fdbc-4463-85f4-86f0f4931b3f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_aeval_mem_pow_250a3eb5ea29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_aeval_monoProd_6aa38ad48f99
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_isHomogeneous_4a7cd1fe755c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619
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
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ} {h : Fin (r + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
theorem _root_.solution (H : SubSystem S x Ω) (I : Chart x) (hh : ∀ l, h l ∈ H.sub I)
    (T : Finset (Fin (r + 1))) (n : ℕ) : (∏ l ∈ T, h l) ^ n ∈ (H.pow (T.card * n)).sub I := by
  refine AmpleTwistLocal.pow_mem_pow H I ?_ n
  rw [SubSystem.pow_sub, ← AmpleAffineGen.aeval_monoProd (S := S)]
  exact aeval_mem_pow hh (AmpleAffineGen.monoProd_isHomogeneous T)
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
