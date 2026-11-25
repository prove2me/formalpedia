-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gramHess_form_80017e7b56b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:35.52086+00:00
-- url     : https://prove2.me/submissions/d75bbfe3-dc72-42fb-9036-b7965c90e210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHessianComparison
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartHessianComparison
theorem _root_.solution (u : F) (d : Fin e → F) (x : Fin e → ℂ) :
    star x ⬝ᵥ (gramHess u d *ᵥ x) =
      (⟪u, u⟫_ℂ * ⟪∑ i, star (x i) • d i, ∑ i, star (x i) • d i⟫_ℂ -
        ⟪u, ∑ i, star (x i) • d i⟫_ℂ * ⟪∑ i, star (x i) • d i, u⟫_ℂ) / (2 * ⟪u, u⟫_ℂ ^ 2) := by
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_mul_sum]
  simp only [dotProduct, mulVec, gramHess, of_apply, Pi.star_apply, Complex.star_def,
    Complex.conj_conj, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GroundTheory.Heights₂.Heights.ChartHessianComparison
