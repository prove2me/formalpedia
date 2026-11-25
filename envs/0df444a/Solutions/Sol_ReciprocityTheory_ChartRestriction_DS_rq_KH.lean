-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rq_KH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:41.904631+00:00
-- url     : https://prove2.me/submissions/73aff505-b75f-45f0-9b3d-dd769153b224

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_K_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_K_JH

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
    kᴴ ∈ Kset ε := by
  refine ⟨?_, rq_K_JH hk⟩
  rw [Matrix.mem_unitaryGroup_iff]
  show kᴴ * kᴴᴴ = 1
  rw [Matrix.conjTranspose_conjTranspose]
  exact (rq_K_unit hk).1
end ReciprocityTheory.ChartRestriction.DS
