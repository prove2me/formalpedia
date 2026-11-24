-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_proof_793669600b5a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:36.992824+00:00
-- url     : https://prove2.me/submissions/646e693e-214a-45a3-8bbd-15af26f1dc6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_weight_blockWeight_apply_e50de9fe3a17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_eval__monomial_cone_2bc04389d40a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue
namespace GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue
theorem _root_.solution : ProjIdealFormValue.Statement := by
  intro F _ Ω _ _ K _ ι y N E _ _ w M φ Φ _ _ t d x hx
  have hx' : IsWeightedHomogeneous (blockWeight (bundleIdx ι M)) x d := hx
  rw [projIdeal, RingHom.mem_ker, coe_eval₂Hom]
  by_cases hx0 : x = 0
  · subst hx0
    simp
  obtain ⟨m₀, hm₀⟩ : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hx0
  have hD : ∀ m ∈ x.support, Finsupp.mapDomain Sigma.fst m = Finsupp.mapDomain Sigma.fst m₀ := by
    intro m hm
    ext o
    rw [← weight_blockWeight_apply, ← weight_blockWeight_apply, hx' (mem_support_iff.mp hm),
      hx' (mem_support_iff.mp hm₀)]
  have key : eval₂ (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
      (fun p => C (projCoord y w φ t p) * X p.1) x =
      C (eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) x) *
        monomial (Finsupp.mapDomain Sigma.fst m₀) 1 := by
    conv_lhs => rw [x.as_sum]
    conv_rhs => rw [x.as_sum]
    rw [eval₂_sum, eval₂_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval₂_monomial_cone, hD m hm]
  rw [key, mul_eq_zero, C_eq_zero, monomial_eq_zero]
  simp
end GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue
