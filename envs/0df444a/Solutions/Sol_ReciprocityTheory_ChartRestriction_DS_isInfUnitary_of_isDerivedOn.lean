-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:36.782907+00:00
-- url     : https://prove2.me/submissions/90d8798f-5c8e-429d-bfbd-9621dd6fcb68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_actM_smul__ee45d6d95b18
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_actM_single__1981af085db5
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inner_actM_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_theta_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) :
    IsInfUnitary ε E := by
  unfold IsInfUnitary
  intro a b v w
  rw [← actM_single' E a b, inner_actM_eq hσ hD, theta_single, actM_smul', actM_single']
  rw [LinearMap.smul_apply, inner_smul_right]
end ReciprocityTheory.ChartRestriction.DS
