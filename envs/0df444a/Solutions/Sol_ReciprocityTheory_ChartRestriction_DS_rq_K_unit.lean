-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rq_K_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:16.302434+00:00
-- url     : https://prove2.me/submissions/ddaa720f-5bcc-463c-b3d0-6a73415412bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose

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
    kᴴ * k = 1 ∧ k * kᴴ = 1 := by
  obtain ⟨hu, -⟩ := hk
  exact ⟨Matrix.mem_unitaryGroup_iff'.mp hu, Matrix.mem_unitaryGroup_iff.mp hu⟩
end ReciprocityTheory.ChartRestriction.DS
