-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_xProd_pow_mem_fd9a69082dcf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:27:50.77482+00:00
-- url     : https://prove2.me/submissions/cab651b5-b919-406e-aff9-d42e01a005e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_aeval_mem_pow_250a3eb5ea29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_eq_monoProd_pow_1a8c10e5c337
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_aeval_monoProd_6aa38ad48f99
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_isHomogeneous_4a7cd1fe755c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_xProd_ne_zero_5c3b01ddff8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_isHomogeneous_bb0f48dbdc12


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
    (J : Chart h) {a : Ω} (ha : a ∈ chartRing S h J) :
    ∃ k : ℕ, a * xProd J ^ k ∈ (H.pow (J.1.card * k)).sub I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  obtain ⟨k, t, ht, hst⟩ := exists_mul_eq_monoProd_pow hs
  obtain ⟨d, htd⟩ := monos_isHomogeneous ht
  have hval : aeval h s * aeval h t = xProd J ^ k := by
    rw [← map_mul, hst, map_pow, AmpleAffineGen.aeval_monoProd]; rfl
  have hne : AmpleAffineGen.monoProd (S := S) J.1 ^ k ≠ 0 := by
    intro h0
    have := congrArg (aeval h) h0
    rw [map_pow, AmpleAffineGen.aeval_monoProd, map_zero] at this
    exact pow_ne_zero _ (AmpleAffineGen.xProd_ne_zero J) this
  have hdeg : e + d = J.1.card * k := by
    have h1 := hse.mul htd
    rw [hst] at h1
    exact h1.inj_right ((AmpleAffineGen.monoProd_isHomogeneous J.1).pow k) hne
  refine ⟨k, ?_⟩
  have hs0 : aeval h s ≠ 0 := eval_ne_zero_of_mem_monos J hs
  have e1 : aeval h f / aeval h s * xProd J ^ k = aeval h (f * t) := by
    rw [← hval, map_mul]; field_simp
  rw [e1, SubSystem.pow_sub, ← hdeg]
  exact aeval_mem_pow hh (hf.mul htd)
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
