-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_mem_chartRing_mul_pow_34215a6d5d99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:26.586902+00:00
-- url     : https://prove2.me/submissions/0bb6f638-309f-42c5-869a-ac49649c5f1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_xProd_ne_zero_1ea80b10c369
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_eq_prod_pow_4e53c7d5cb35

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
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (I J : Chart x) {c : Ω} (hc : c ∈ chartRing k x J) :
    ∃ (c' : Ω) (m : ℕ), c' ∈ chartRing k x I ∧
      c = c' * (xProd I ^ J.1.card / xProd J ^ I.1.card) ^ m := by
  classical
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  obtain ⟨t, m, d, ht, hst⟩ := exists_mul_eq_prod_pow (k := k) hs
  have hs0 := eval_ne_zero_of_mem_monos J hs
  have hJ0 : xProd J ≠ 0 := xProd_ne_zero J
  have hI0 : xProd I ≠ 0 := xProd_ne_zero I
  have hevJ : aeval x (∏ i ∈ J.1, (X i : Poly k N)) = xProd J := by simp [xProd, map_prod]
  have hevI : aeval x (∏ i ∈ I.1, (X i : Poly k N)) = xProd I := by simp [xProd, map_prod]
  have hst' : aeval x s * aeval x t = xProd J ^ m := by rw [← map_mul, hst, map_pow, hevJ]
  have ht0 : aeval x t ≠ 0 := right_ne_zero_of_mul (hst' ▸ pow_ne_zero m hJ0)
  have hpJ : (∏ i ∈ J.1, (X i : Poly k N)).IsHomogeneous J.1.card := by
    simpa using IsHomogeneous.prod J.1 (fun i => (X i : Poly k N)) (fun _ => 1)
      fun i _ => isHomogeneous_X k i
  have hpI : (∏ i ∈ I.1, (X i : Poly k N)).IsHomogeneous I.1.card := by
    simpa using IsHomogeneous.prod I.1 (fun i => (X i : Poly k N)) (fun _ => 1)
      fun i _ => isHomogeneous_X k i
  have hdeg : e + d = J.1.card * m := by
    have h2 : (s * t).IsHomogeneous (J.1.card * m) := by rw [hst]; exact hpJ.pow m
    have hne : s * t ≠ 0 := by
      rw [hst]
      exact pow_ne_zero _ fun h0 => hJ0 (by rw [← hevJ, h0, map_zero])
    exact (hse.mul ht).inj_right h2 hne
  obtain ⟨i', hi'⟩ : ∃ i', I.1.card = i' + 1 :=
    ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  refine ⟨aeval x (f * t * (∏ i ∈ J.1, X i) ^ (m * i')) /
      aeval x ((∏ i ∈ I.1, X i) ^ (m * J.1.card)), m,
    ⟨f * t * (∏ i ∈ J.1, X i) ^ (m * i'), (∏ i ∈ I.1, X i) ^ (m * J.1.card),
      I.1.card * (m * J.1.card),
      pow_mem (Submonoid.prod_mem _ fun i hi => X_mem_monos hi) _, ?_, hpI.pow _, rfl⟩, ?_⟩
  · have h3 := (hf.mul ht).mul (hpJ.pow (m * i'))
    convert h3 using 1
    rw [hdeg, hi']
    ring
  · have key : aeval x f / aeval x s = aeval x f * aeval x t / xProd J ^ m := by
      rw [← hst', mul_div_mul_right _ _ ht0]
    rw [key]
    simp only [map_mul, map_pow, hevJ, hevI]
    rw [hi', div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm,
      div_eq_div_iff (pow_ne_zero _ hJ0) (mul_ne_zero (pow_ne_zero _ hI0) (pow_ne_zero _ hJ0))]
    ring
end GroundTheory.Heights₂.Heights.Kleiman
