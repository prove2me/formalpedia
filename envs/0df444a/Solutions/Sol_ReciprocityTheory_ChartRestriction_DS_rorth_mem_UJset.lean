-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_mem_UJset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:36.013632+00:00
-- url     : https://prove2.me/submissions/6de419ae-315d-493f-be04-433c92078693

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero

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
  obtain ⟨hu, hJ⟩ := hk
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff'.1 hu)
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, h1, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.DS
