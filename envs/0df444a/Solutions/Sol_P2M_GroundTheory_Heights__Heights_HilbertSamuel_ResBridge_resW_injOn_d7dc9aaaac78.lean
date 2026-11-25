-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resW_injOn_d7dc9aaaac78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:32:08.953733+00:00
-- url     : https://prove2.me/submissions/52cb9efc-ee76-4428-8aa9-4d2d59a76cc8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_mem_4c5488d76894
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sameOrbit_of_segre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
theorem _root_.solution (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set.InjOn (resW R Ψ) {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  refine R.R.inj (R.idx x) (R.idx x') x (R.mem_src_idx x) x' (R.mem_src_idx x') hx.1 ?_
  have hseg : segre (R.pt x) = (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) • segre (R.pt x') := by
    have := congrArg (fun v => Ψ (segre (R.pt x)) 0 • v) hw
    simp only [resW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
    exact this
  obtain ⟨c, hc, h⟩ := sameOrbit_of_segre
    (GroundTheory.Heights₂.Heights.Inter.res_mem R x' (R.mem_src_idx x')).1
    (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) (by simp [hx.2, hx'.2]) hseg
  exact ⟨c, hc, h⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
