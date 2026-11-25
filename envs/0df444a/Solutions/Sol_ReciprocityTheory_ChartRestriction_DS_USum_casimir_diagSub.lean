-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.casimir_diagSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:18.079373+00:00
-- url     : https://prove2.me/submissions/3f6ee8e1-d01d-44c9-85f6-3d1e37cf68a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_DiagSubIsKIrrHW
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_USum_diag__apply_d051f1906fda
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_casimir_sE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_lift_ofP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix WithLp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ} {ε : Fin n → Bool}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution (φ : V₁ →ₗ[ℂ] V₂) {c : ℂ}
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = c • v) (hc₂ : ∀ v ∈ V₂, casimir E₂ v = c • v) :
    ∀ x ∈ diagSub φ, casimir (sE E₁ E₂) x = c • x := by
  intro x hx
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
  rw [casimir_sE, diagι_apply]
  simp only [lift_ofP]
  rw [hc₁ _ v.2, hc₂ _ (φ v).2, ← Prod.smul_mk, map_smul]
end ReciprocityTheory.ChartRestriction.DS.USum
