-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.mem_ncV_iff_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:01.637844+00:00
-- url     : https://prove2.me/submissions/2bb96437-38c0-4a93-9812-0b54701a0f3b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ : Fin k → Fin n × Fin n,
      F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  rfl
end ReciprocityTheory.ChartRestriction.DS
