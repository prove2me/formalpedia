-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kLowSpan_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:20.407816+00:00
-- url     : https://prove2.me/submissions/17c9a949-c701-4d22-a374-5cf573264a9b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {y : M} {T : Submodule ℂ M} (hT : IsKStableSub ε E T) (hy : y ∈ T) :
    kLowSpan ε E y ≤ T := by
  have hW : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → lowWord E y l ∈ T := by
    intro l
    induction l with
    | nil => intro _; exact hy
    | cons p l ih =>
      intro hl
      have hp : p.2 < p.1 ∧ ε p.1 = ε p.2 := hl p (by simp)
      exact hT p.1 p.2 hp.2 _ (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
  unfold kLowSpan
  rw [Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  exact hW l hl
end ReciprocityTheory.ChartRestriction.DS
