-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kirrSpan_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:20.011532+00:00
-- url     : https://prove2.me/submissions/5496f481-b3db-4517-af0a-2f787e7e4d77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr

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
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hV : IsKStableSub ε A V) {u : X} (hu : u ∈ V) : kirrSpan ε A u ≤ V := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => exact hu
  | cons p l ih =>
    exact hV p.1 p.2 (hl p (by simp)).2 _ (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)))
end ReciprocityTheory.ChartRestriction.DS
