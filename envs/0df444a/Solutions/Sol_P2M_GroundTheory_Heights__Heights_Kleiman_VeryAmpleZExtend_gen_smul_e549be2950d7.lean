-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_gen_smul_e549be2950d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:40.541976+00:00
-- url     : https://prove2.me/submissions/c65ac255-c65c-40ba-aac8-7df28ee34657

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_prod_mem_pow_64615a997730
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_smul_mem_twist_pow_e1c974636e30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619


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
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
theorem _root_.solution {r : ℕ} (F : SubSystem S x E) (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (I : Chart x) (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) {c : Ω} {a : ℕ}
    (hc : c * h j ^ a ∈ (H.pow a).sub I) {y : E}
    (hy : ∃ m : ℕ, xProd J ^ m • y ∈ (F.twist (H.pow (J.1.card * m))).sub I) :
    ∃ m : ℕ, xProd J ^ m • (c • y) ∈ (F.twist (H.pow (J.1.card * m))).sub I := by
  classical
  obtain ⟨m, hm⟩ := hy
  have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
  have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
  have hw := AmpleTwistLocal.mul_mem_pow H I hc _
    (AmpleTwistLocal.pow_mem_pow H I (prod_mem_pow H hh I (J.1.erase j)) a)
  refine ⟨m + a, ?_⟩
  have e1 : xProd J ^ (m + a) • (c • y) =
      (c * h j ^ a * (∏ l ∈ J.1.erase j, h l) ^ a) • (xProd J ^ m • y) := by
    rw [smul_smul, smul_smul, hJ]
    congr 1
    ring
  have e2 : J.1.card * (m + a) = J.1.card * m + (a + (J.1.erase j).card * a) := by
    rw [← hcard]; ring
  rw [e1, e2]
  exact smul_mem_twist_pow F H I hm hw
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
