-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rq_K_JH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:06.093628+00:00
-- url     : https://prove2.me/submissions/1af0672b-e563-485e-8cf4-cfdd5287a215

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_K_unit

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
theorem _root_.solution {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ * Jm ε = Jm ε * kᴴ := by
  obtain ⟨h1, h2⟩ := rq_K_unit hk
  have hc : k * Jm ε = Jm ε * k := hk.2
  calc kᴴ * Jm ε = kᴴ * Jm ε * (k * kᴴ) := by rw [h2, mul_one]
    _ = kᴴ * (Jm ε * k) * kᴴ := by simp only [mul_assoc]
    _ = kᴴ * (k * Jm ε) * kᴴ := by rw [hc]
    _ = kᴴ * k * Jm ε * kᴴ := by simp only [mul_assoc]
    _ = Jm ε * kᴴ := by rw [h1, one_mul]
end ReciprocityTheory.ChartRestriction.DS
