-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_VanishNearPoint_proof_94402769fc91
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:27.29226+00:00
-- url     : https://prove2.me/submissions/9ca62e4b-2fbe-4344-a900-b116e2a3ca5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVanishNearPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVanishNearPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace VanishNearPoint
theorem _root_.solution (hOpen : FiniteMapOpen.Statement) : VanishNearPoint.Statement := by
  classical
  intro n J f x hJ hx hf
  by_contra hfJ
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ.ne_top
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ J)
  choose p hp using fun i => Ideal.Quotient.mk_surjective (g (X i))
  have hg : g = (Ideal.Quotient.mkₐ ℂ J).comp (aeval p) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hp]
  subst hg
  let _ := ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom.toAlgebra
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) :=
    RingHom.IsIntegral.of_finite hfin _
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨h, hh, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hh
  obtain ⟨a, ha⟩ := hh
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hJmem : aeval p h - q * f ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero]
    exact ha.symm

  have hval : ∀ z ∈ zeroLocus J, eval (fun i => eval z (p i)) h = eval z q * eval z f := by
    intro z hz
    have h1 := hz _ hJmem
    rw [map_sub, map_mul, sub_eq_zero] at h1
    rw [← h1]
    have h2 := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℂ) (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (f := p)) h
    rw [AlgHom.comp_apply] at h2
    exact h2.symm
  have hV := hOpen n d J p hJ hinj hfin x hx _ hf
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  apply hh0
  refine MvPolynomial.funext_set (fun i => Metric.ball (eval x (p i)) ε)
    (fun i => infinite_of_mem_nhds _ (Metric.ball_mem_nhds _ hε)) fun w hw => ?_
  rw [← ball_pi _ hε] at hw
  obtain ⟨z, ⟨hz, hzU⟩, rfl⟩ := hball hw
  rw [hval z hz, hzU hz, mul_zero, map_zero]
end VanishNearPoint
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
