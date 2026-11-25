-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pullbackDensity_holds_pullQ_eq_local_b647b2495787
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:19.203409+00:00
-- url     : https://prove2.me/submissions/c7e1cd70-8fb6-43f9-bd44-caf1bc82138a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsSheetPullW
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_smul
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter
open GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}
  (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
omit [Fintype K']
namespace GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds
theorem _root_.solution (hv : IsBlockMap κ v) {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Ψ z = fun i => Ψ (segre (fun p => R.lift x z (v p))) i.succ /
      Ψ (segre (fun p => R.lift x z (v p))) 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  have hpt : pullPt R v z = fun p => c (κ p.1) * R.lift x z (v p) := by
    funext p
    simp only [pullPt, hzc, hv.2.2.1 p]
  have hpc : ∏ k, c (κ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)
  have hsm := segre_smul (fun k => c (κ k)) (fun p => R.lift x z (v p))
  funext i
  simp only [pullQ, hpt, hsm, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc
end GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds
