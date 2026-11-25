-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.derived_adK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:36.729357+00:00
-- url     : https://prove2.me/submissions/1ebc94a3-c4db-4d21-8bad-0447a193afad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_main_G
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_inG_S
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isInLieAlgebra_I_smul_add_conjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_decomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_lin

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
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (X : Matrix (Fin n) (Fin n) ℂ) (v : D) :
    σ k ((actM E X v : D) : H) =
      ((actM E (k * X * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
  have hS := rq_main_G hσ hD hk (rq_inG_S ε X) v
  have hT := rq_main_G hσ hD hk (isInLieAlgebra_I_smul_add_conjTranspose ε X) v
  have := rq_lin hD hk v (1 / 2 : ℂ) (-(Complex.I / 2)) hS hT
  rwa [rq_decomp] at this
end ReciprocityTheory.ChartRestriction.DS
