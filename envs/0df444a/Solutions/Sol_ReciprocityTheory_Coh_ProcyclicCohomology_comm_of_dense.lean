-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.comm_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:22.460925+00:00
-- url     : https://prove2.me/submissions/3f9a0d0b-5d31-496b-a608-52459bb9afaf

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot

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
namespace ReciprocityTheory.Coh.ProcyclicCohomology
theorem _root_.solution [T2Space G] {s : G} (hs : Dense (Subgroup.zpowers s : Set G)) (a b : G) :
    a * b = b * a := by
  have hcl : IsClosed {p : G × G | p.1 * p.2 = p.2 * p.1} :=
    isClosed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst)
  have hd : Dense ((Subgroup.zpowers s : Set G) ×ˢ (Subgroup.zpowers s : Set G)) := hs.prod hs
  have hsub : (Subgroup.zpowers s : Set G) ×ˢ (Subgroup.zpowers s : Set G) ⊆
      {p : G × G | p.1 * p.2 = p.2 * p.1} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact zpow_mul_comm s i j
  have h := hcl.closure_subset_iff.2 hsub
  rw [hd.closure_eq] at h
  exact h (Set.mem_univ (a, b))
end ReciprocityTheory.Coh.ProcyclicCohomology
