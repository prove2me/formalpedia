-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_USum_coe_diag__b625a3818ad7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:36.411466+00:00
-- url     : https://prove2.me/submissions/3ab27467-b6b4-4729-9beb-0aae547aeb03

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_DiagSubIsKIrrHW

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
theorem _root_.solution (φ : V₁ →ₗ[ℂ] V₂) (v : V₁) :
    ((diagι φ v : sD D₁ D₂) : WithLp 2 (H₁ × H₂)) =
      toLp 2 (((v : D₁) : H₁), (((φ v : V₂) : D₂) : H₂)) := rfl
end ReciprocityTheory.ChartRestriction.DS.USum
