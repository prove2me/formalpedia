-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rq_K_UJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:06.150254+00:00
-- url     : https://prove2.me/submissions/4250a633-2a84-4d7b-a4d5-02d4e97d6357

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
    k ∈ UJset ε := by
  have hc : k * Jm ε = Jm ε * k := hk.2
  show kᴴ * Jm ε * k = Jm ε
  rw [mul_assoc, ← hc, ← mul_assoc, (rq_K_unit hk).1, one_mul]
end ReciprocityTheory.ChartRestriction.DS
