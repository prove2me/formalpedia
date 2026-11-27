-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_UniformiserGradientIndependent_proof_d026d4472dc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:11:29.220753+00:00
-- url     : https://prove2.me/submissions/8daf0aa5-d5fc-4469-8c01-992c9facc5d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserGradientIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveJacobian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurvePointDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUniformiserGradientIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_apply_6330d6b8766e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_of_eval_eq_zero_a46392587438
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_mem_sq_of_grad_eq_zero_7cd8970785ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_pointLocalRing_0914499906a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_pointLocalRing_eval_ne_zero_of_isUnit_a20956d1da78


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
namespace GroundTheory.Heights₂.Heights
namespace UniformiserGradientIndependent
theorem _root_.solution (hjac : NormalCurveJacobian.Statement)
    (hdvr : NormalCurvePointDVR.Statement) : UniformiserGradientIndependent.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, -, hk, hfI, hli, -, -⟩ := hjac σ I w hI hic hdim hw
  obtain ⟨_, _⟩ := hdvr σ I w hI hic hdim hw
  refine ⟨k, f, hk, hfI, hli.finCons fun hmem ↦ ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  set φ := algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) with hφ
  have hfw : ∀ j, eval w (f j) = 0 := fun j ↦ hw (f j) (hfI j)
  have htw : eval w t = 0 := by
    by_contra h
    exact ht.not_isUnit (isUnit_algebraMap_pointLocalRing I w t h)
  set p := t - ∑ j, C (c j) * f j with hp
  have hpm : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) := by
    simp [hp, RingHom.mem_ker, htw, hfw]
  have hpg : GradientAtPoint.grad w p = 0 := by
    rw [hp, map_sub, map_sum]
    simp_rw [GradientAtPoint.grad_mul_of_eval_eq_zero w _ _ (hfw _), eval_C]
    have hg : ∀ q, GradientAtPoint.grad w q = fun i ↦ eval w (pderiv i q) :=
      fun q ↦ funext (GradientAtPoint.grad_apply w q)
    simp_rw [hg]
    exact sub_eq_zero.2 hc.symm
  have hp2 := GradientAtPoint.mem_sq_of_grad_eq_zero w hpm hpg
  have hφf : ∀ j, φ (f j) = 0 := fun j ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ (hfI j))
  have hφt : φ t = φ p := by simp [hp, hφf]
  have hmax : Ideal.map φ (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ≤
      IsLocalRing.maximalIdeal (pointLocalRing I w) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu ↦ pointLocalRing_eval_ne_zero_of_isUnit I w hw g hu (RingHom.mem_ker.1 hg)
  have ht2 : φ t ∈ IsLocalRing.maximalIdeal (pointLocalRing I w) ^ 2 := by
    rw [hφt]
    exact Ideal.pow_right_mono hmax 2 (Ideal.map_pow φ _ 2 ▸ Ideal.mem_map_of_mem φ hp2)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 ht, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at ht2
  obtain ⟨a, ha⟩ := ht2
  have h1 : φ t * (a * φ t) = φ t * 1 := by rw [mul_one]; nth_rewrite 3 [← ha]; ring
  exact ht.not_isUnit
    (IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact mul_left_cancel₀ ht.ne_zero h1))
end UniformiserGradientIndependent
end GroundTheory.Heights₂.Heights
