-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_isMultiHomog_curveChartMono_8c3e1926fba1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:51.882191+00:00
-- url     : https://prove2.me/submissions/426128d3-1ef4-4f3c-ae55-dbc815017826

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_sum_single_chart_apply_20a2db6e8f85
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (curveChartMono c d) d := by
  classical
  have h : curveChartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
    rw [curveChartMono, monomial_sum_one]
    exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
  have hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d := by
    funext k
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_chart_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  have hm := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial (ι := ι)
    (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)
  rw [hd] at hm
  exact hm
end GroundTheory.Heights₂.Heights.Targets
