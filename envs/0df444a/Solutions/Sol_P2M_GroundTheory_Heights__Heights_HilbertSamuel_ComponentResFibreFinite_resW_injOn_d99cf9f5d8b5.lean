-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_resW_injOn_d99cf9f5d8b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:41:39.745241+00:00
-- url     : https://prove2.me/submissions/9a3bbde9-a501-4031-8481-c052d95f0847

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComponentResFibreFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_pt_mem_conePts_b7c8ef543411
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
theorem _root_.solution (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set.InjOn (resW R Ψ)
      {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  have hseg : segre (R.pt x) =
      (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) • segre (R.pt x') := by
    have := congrArg (fun v => Ψ (segre (R.pt x)) 0 • v) hw
    simp only [resW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
    exact this
  obtain ⟨c, hc, hcz⟩ := sameOrbit_of_segre (pt_mem_conePts R x').1 _ (by simp [hx.2, hx'.2]) hseg
  exact R.R.inj (R.idx x) (R.idx x') x (R.mem_src_idx x) x' (R.mem_src_idx x') hx.1 ⟨c, hc, hcz⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
