-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sch_permute_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:27.257494+00:00
-- url     : https://prove2.me/submissions/8c1f7ea6-aec8-46a5-ae18-a87b9195bd65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchPhiOneApply

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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) : permute σ F κ = F (κ ∘ σ) := rfl
end ReciprocityTheory.ChartRestriction.DS
