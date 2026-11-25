-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_USum_sE_diag__c40f84c7b864
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:56:15.784228+00:00
-- url     : https://prove2.me/submissions/82cd32c2-1a10-44b2-bf23-92fc5a8d2db4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_DiagSubIsKIrrHW
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_USum_diag__apply_d051f1906fda
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
theorem _root_.solution (φ : V₁ →ₗ[ℂ] V₂) (hst : IsKStableSub ε E₁ V₁)
    (hcomm : ∀ a b (hab : ε a = ε b) (v : V₁),
      E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hst a b hab _ v.2⟩ : V₂) : D₂))
    {a b : Fin n} (hab : ε a = ε b) (v : V₁) :
    sE E₁ E₂ a b (diagι φ v) = diagι φ ⟨E₁ a b v, hst a b hab _ v.2⟩ := by
  rw [diagι_apply, diagι_apply]
  simp only [sE, lift_ofP]
  rw [hcomm a b hab v]
end ReciprocityTheory.ChartRestriction.DS.USum
