-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHomogenise_exists_homogeneous_sub_mem_span_2f27af3c3435
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:14.012634+00:00
-- url     : https://prove2.me/submissions/f153b900-f5ae-4e07-89c9-9c847bbdaf7f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise

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
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHomogenise
attribute [local instance] MvPolynomial.gradedAlgebra
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartHomogenise
theorem _root_.solution (ℓ g : MvPolynomial (Fin n) F) (hℓ : ℓ.IsHomogeneous 1) :
    ∃ (G : MvPolynomial (Fin n) F) (D : ℕ), G.IsHomogeneous D ∧ G - g ∈ Ideal.span {ℓ - 1} := by
  classical
  refine ⟨∑ d ∈ Finset.range (g.totalDegree + 1), ℓ ^ (g.totalDegree - d) * homogeneousComponent d g,
    g.totalDegree, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun d hd => ?_
    have hdD : d ≤ g.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have h := (hℓ.pow (g.totalDegree - d)).mul (homogeneousComponent_isHomogeneous d g)
    rwa [one_mul, Nat.sub_add_cancel hdD] at h
  · have e : ∑ d ∈ Finset.range (g.totalDegree + 1), ℓ ^ (g.totalDegree - d) * homogeneousComponent d g - g =
        ∑ d ∈ Finset.range (g.totalDegree + 1), (ℓ ^ (g.totalDegree - d) - 1) * homogeneousComponent d g := by
      simp only [sub_one_mul, Finset.sum_sub_distrib, sum_homogeneousComponent]
    rw [e]
    refine Ideal.sum_mem _ fun d _ => Ideal.mul_mem_right _ _ ?_
    rw [Ideal.mem_span_singleton]
    simpa using sub_dvd_pow_sub_pow ℓ 1 (g.totalDegree - d)
end GroundTheory.Heights₂.Heights.ChartHomogenise
