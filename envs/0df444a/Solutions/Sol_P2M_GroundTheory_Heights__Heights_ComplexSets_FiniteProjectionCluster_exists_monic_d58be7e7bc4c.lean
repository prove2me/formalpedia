-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_monic_d58be7e7bc4c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:04.090027+00:00
-- url     : https://prove2.me/submissions/84a31b9c-a952-429b-b7ac-dababa9e7a16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Topology
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (j : Fin n) :
    ∃ P : Polynomial (MvPolynomial (Fin d) ℂ), P.Monic ∧
      ∀ x ∈ zeroSet J, (P.map (eval (A.mulVec x))).IsRoot (x j) := by
  obtain ⟨P, hPm, hP⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk J (X j))
  refine ⟨P, hPm, fun x hx => ?_⟩
  have hf : (projHom J A).toRingHom = (Ideal.Quotient.mk J).comp (pullback A).toRingHom := rfl
  rw [hf, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem] at hP
  have h0 := hx _ hP
  rw [Polynomial.hom_eval₂, eval_X] at h0
  have hcomp : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x) :=
    RingHom.ext (FibreBound.eval_pullback A x)
  rw [hcomp, Polynomial.eval₂_eq_eval_map] at h0
  exact h0
end GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster
