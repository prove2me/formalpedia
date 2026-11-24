-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_fibre_finite_7d46f66826ee
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:30.998343+00:00
-- url     : https://prove2.me/submissions/af11fedf-0c73-4b70-8848-392fca9869ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_monic_d58be7e7bc4c

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
    (hA : IsFiniteProjection J A) (y : Fin d → ℂ) :
    {x | x ∈ zeroSet J ∧ A.mulVec x = y}.Finite := by
  choose P hPm hP using exists_monic J A hA
  refine (Set.Finite.pi (t := fun j => {a | ((P j).map (eval y)).IsRoot a})
    fun j => Polynomial.finite_setOfPred_isRoot ((hPm j).map _).ne_zero).subset ?_
  rintro x ⟨hx, hxA⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  intro j
  rw [← hxA]
  exact hP j x hx
end GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster
