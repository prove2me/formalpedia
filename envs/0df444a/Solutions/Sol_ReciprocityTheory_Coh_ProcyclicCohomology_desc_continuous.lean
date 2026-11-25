-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.desc_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:31.396093+00:00
-- url     : https://prove2.me/submissions/c187652f-9613-49cd-b492-968bf6fbb9e6

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_desc_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Coh.ProcyclicCohomology
open Topology
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {s : G}
namespace ReciprocityTheory.Coh.ProcyclicCohomology
theorem _root_.solution [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G))
    (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*} [TopologicalSpace X] (T : ℕ → X)
    (hper : ∀ j, T (j + W.index) = T j) : Continuous (desc W h T) := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hU : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (W : Set G)) :=
    hW.preimage (continuous_const.mul continuous_id)
  have hg : g ∈ (fun y => g⁻¹ * y) ⁻¹' (W : Set G) := by simp [W.one_mem]
  refine (continuousAt_const : ContinuousAt (fun _ : G => desc W h T g) g).congr ?_
  filter_upwards [hU.mem_nhds hg] with y hy
  have h0 := Classical.choose_spec (h g)
  have hy' : y⁻¹ * s ^ Classical.choose (h g) ∈ W := by
    have hw := W.mul_mem (W.inv_mem hy) h0
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at hw
    exact hw
  rw [desc_eq hc hs hW h T hper hy']
  rfl
end ReciprocityTheory.Coh.ProcyclicCohomology
