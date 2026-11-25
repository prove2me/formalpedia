-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_normSegre_sameOrbit_b77e8e882eac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:35.058666+00:00
-- url     : https://prove2.me/submissions/258d3a34-8473-4b64-b319-d0c0813fef00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOver
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NormSegreSameOrbit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_smul


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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K'] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount
theorem _root_.solution {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {z₁ z₂ : (Σ k', ι' k') → ℂ} (h : SameOrbit z₁ z₂) :
    (Ψ (segre fun p => z₁ (v p)) 0)⁻¹ • segre (fun p => z₁ (v p)) =
      (Ψ (segre fun p => z₂ (v p)) 0)⁻¹ • segre (fun p => z₂ (v p)) := by
  obtain ⟨c, hc, rfl⟩ := h
  have h1 : (fun p => c (v p).1 * z₂ (v p)) = fun p : Σ k, ι k => (c ∘ κ) p.1 * z₂ (v p) := by
    funext p
    rw [hv.2.2.1 p]
    rfl
  have hne : ∏ k, (c ∘ κ) k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)
  rw [h1, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hne, mul_one]
end GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount
