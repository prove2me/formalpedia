-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_secIdeal_f302b2e73333
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:26.685109+00:00
-- url     : https://prove2.me/submissions/f761745b-1b2b-439d-9f73-dd30d3d6faeb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_linForm_b42ca2da91cd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
variable {k : Type} [Field k] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
theorem _root_.solution (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
        (X : Par e n → MvPolynomial (Par e n) k)).map
        (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n))) =
      secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n) := by
  have h1 : (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k))).map
      (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n))) =
      Q.map (MvPolynomial.map (algebraMap k (GenParField k e n))) := by
    rw [Ideal.map_map]
    congr 1
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, MvPolynomial.map_map,
      IsScalarTower.algebraMap_eq k (MvPolynomial (Par e n) k) (GenParField k e n), MvPolynomial.algebraMap_eq]
  have h2 : (Ideal.span (Set.range (secForm (X : Par e n → MvPolynomial (Par e n) k)))).map
      (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n))) =
      Ideal.span (Set.range (secForm (genPar k e n))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp only [Function.comp_apply, secForm, map_linForm]
    rfl
  have h3 : (Ideal.span {chartForm (X : Par e n → MvPolynomial (Par e n) k) - 1}).map
      (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n))) =
      Ideal.span {chartForm (genPar k e n) - 1} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one, chartForm, chartForm, map_linForm]
    rfl
  rw [secIdeal, secIdeal, Ideal.map_sup, Ideal.map_sup, h1, h2, h3]
end GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
