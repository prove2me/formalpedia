-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_proof_ef1da2e4d158
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:00:55.640933+00:00
-- url     : https://prove2.me/submissions/8292fe02-8f2d-4903-9a85-61128e0a068c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartScalingIndep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_coeff_eq_zero_674c17c17c2e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
namespace GroundTheory.Heights₂.Heights.Inter
namespace ChartScalingIndep
theorem _root_.solution : ChartScalingIndep.Statement := by
  classical
  intro F Ω _ _ _ K _ ι _ x i hx hV
  set y : (Σ k, ι k) → Ω := fun q => x q / x ⟨q.1, i q.1⟩ with hy
  rw [algebraicIndependent_iff]
  intro p hp

  have hq : ∀ α, ∃ a b : MRingOver F ι, aeval y b ≠ 0 ∧
      ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) * aeval y b = aeval y a := by
    intro α
    obtain ⟨r, hr, t, ht, he⟩ := IntermediateField.mem_adjoin_iff_div.mp (p.coeff α).2
    rw [Algebra.adjoin_range_eq_range_aeval] at hr ht
    obtain ⟨a, rfl⟩ := hr
    obtain ⟨b, rfl⟩ := ht
    change ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) = aeval y a / aeval y b at he
    by_cases hb : aeval y b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [he, hb, div_zero]
      simp
    · exact ⟨a, b, hb, by rw [he, div_mul_cancel₀ _ hb]⟩
  choose a b hb hab using hq
  set D : MRingOver F ι := ∏ α ∈ p.support, b α with hD
  have hD0 : aeval y D ≠ 0 := by
    rw [hD, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun α _ => hb α
  set g : (K →₀ ℕ) → MRingOver F ι := fun α => a α * ∏ β ∈ p.support.erase α, b β with hg
  have hgD : ∀ α ∈ p.support,
      aeval y (g α) = aeval y D * ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) := by
    intro α hα
    rw [hg, hD, map_mul, map_prod, map_prod, ← Finset.mul_prod_erase _ _ hα, ← hab α]
    ring
  have h1 : aeval (fun k => x ⟨k, i k⟩) p = ∑ α ∈ p.support,
      ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) * ∏ k, x ⟨k, i k⟩ ^ α k := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun k => pow_zero _)]
    rfl
  have hsum : ∑ α ∈ p.support, aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k = 0 := by
    calc ∑ α ∈ p.support, aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k
        = aeval y D * aeval (fun k => x ⟨k, i k⟩) p := by
          rw [h1, Finset.mul_sum]
          exact Finset.sum_congr rfl fun α hα => by rw [hgD α hα, mul_assoc]
      _ = 0 := by rw [hp, mul_zero]
  have h0 := ChartScalingIndep.coeff_eq_zero x i hx hV p.support g hsum
  refine MvPolynomial.ext _ _ fun α => ?_
  rw [coeff_zero]
  by_cases hα : α ∈ p.support
  · have h2 := h0 α hα
    rw [hgD α hα] at h2
    have h3 := (mul_eq_zero.mp h2).resolve_left hD0
    exact_mod_cast h3
  · exact notMem_support_iff.mp hα
end ChartScalingIndep
end GroundTheory.Heights₂.Heights.Inter
