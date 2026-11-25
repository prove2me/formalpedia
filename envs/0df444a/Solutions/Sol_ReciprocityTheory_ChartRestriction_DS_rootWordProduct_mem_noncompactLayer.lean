-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rootWordProduct_mem_noncompactLayer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:23.405819+00:00
-- url     : https://prove2.me/submissions/d46fa9e1-acec-4973-9b56-8a31a145bee0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rootWordProduct_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rootWordProduct_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_apply_mem_noncompactLayer_succ

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
theorem _root_.solution : ∀ {k : ℕ} (κ : Fin k → Fin n × Fin n),
    (∀ i, ε (κ i).1 ≠ ε (κ i).2) → ∀ v ∈ V, word E κ v ∈ layer ε E V k
  | 0, κ, _, v, hv => by rw [rootWordProduct_zero]; exact hv
  | k + 1, κ, hκ, v, hv => by
    revert hκ
    refine Fin.consCases (fun p τ => ?_) κ
    intro hκ
    rw [rootWordProduct_cons, Module.End.mul_apply]
    have hp : ε p.1 ≠ ε p.2 := by simpa using hκ 0
    have hτ : ∀ i, ε (τ i).1 ≠ ε (τ i).2 := fun i => by simpa using hκ i.succ
    exact apply_mem_noncompactLayer_succ hp (solution τ hτ v hv)
end ReciprocityTheory.ChartRestriction.DS
