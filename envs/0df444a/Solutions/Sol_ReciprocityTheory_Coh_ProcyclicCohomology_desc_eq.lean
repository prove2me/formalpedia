-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.desc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:55:31.973057+00:00
-- url     : https://prove2.me/submissions/52636375-09d5-4f12-88f0-f7d9567e437b

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_zpow_mem_iff
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_per_of_dvd

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
    (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*} (T : ℕ → X)
    (hper : ∀ j, T (j + W.index) = T j) {g : G} {j : ℕ} (hj : g⁻¹ * s ^ j ∈ W) :
    desc W h T g = T j := by
  have h0 := Classical.choose_spec (h g)
  show T (Classical.choose (h g)) = T j
  have hm : s ^ ((j : ℤ) - (Classical.choose (h g) : ℕ)) ∈ W := by
    have hw := W.mul_mem (W.inv_mem h0) hj
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at hw
    rw [zpow_sub, zpow_natCast, zpow_natCast, hc]
    exact hw
  exact per_of_dvd W.index T hper _ _ ((zpow_mem_iff hc hs hW _).mp hm)
end ReciprocityTheory.Coh.ProcyclicCohomology
