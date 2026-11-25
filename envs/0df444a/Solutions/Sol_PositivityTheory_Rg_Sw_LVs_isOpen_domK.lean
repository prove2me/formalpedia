-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.isOpen_domK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:33:33.912705+00:00
-- url     : https://prove2.me/submissions/8114de40-519a-45d5-b41c-8a212625c7dc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_isOpen_dom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg] (ι : Kg → M2 n) (hι : Continuous ι) :
    IsOpen {x : M2 n | ∀ k, ι k * x ∈ Dom n} := by
  rw [isOpen_iff_mem_nhds]
  intro x0 hx0
  have key : ∀ k ∈ (Set.univ : Set Kg), ∀ᶠ z : M2 n × Kg in nhds (x0, k), ι z.2 * z.1 ∈ Dom n := fun k _ =>
    ((hι.comp continuous_snd).mul continuous_fst).continuousAt.preimage_mem_nhds (isOpen_dom.mem_nhds (hx0 k))
  have h := isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun (x : M2 n) (k : Kg) => ι k * x ∈ Dom n) key
  filter_upwards [h] with x hx k using hx k (Set.mem_univ k)
end PositivityTheory.Rg.Sw.LVs
