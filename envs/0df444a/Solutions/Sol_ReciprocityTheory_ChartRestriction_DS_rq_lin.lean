-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rq_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:52.708827+00:00
-- url     : https://prove2.me/submissions/3c29fa1e-5f02-4e8e-b1f6-5a4dbe77fe6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_actM_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_actM_smul

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : D) (a b : ℂ)
    {S T : Matrix (Fin n) (Fin n) ℂ}
    (hS : σ k ((actM E S v : D) : H) =
      ((actM E (k * S * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H))
    (hT : σ k ((actM E T v : D) : H) =
      ((actM E (k * T * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H)) :
    σ k ((actM E (a • S + b • T) v : D) : H) =
      ((actM E (k * (a • S + b • T) * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
  have e1 : k * (a • S + b • T) * kᴴ = a • (k * S * kᴴ) + b • (k * T * kᴴ) := by
    simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, rq_actM_add, rq_actM_add, rq_actM_smul, rq_actM_smul, rq_actM_smul, rq_actM_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul,
    hS, hT]
end ReciprocityTheory.ChartRestriction.DS
