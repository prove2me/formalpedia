-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.T1.lat_mk_le_of_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:07.654533+00:00
-- url     : https://prove2.me/submissions/8c8c94c6-4c96-4ffe-af12-0b1a46e62b94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlaceB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Cardinal Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T1
namespace ReciprocityTheory.ChartRestriction.T1
theorem _root_.solution {D X : Type} [TopologicalSpace X] [FirstCountableTopology X] [T2Space X]
    (f : D → X) (hf : DenseRange f) : #X ≤ #D ^ ℵ₀ := by
  classical
  have hseq : ∀ x : X, ∃ u : ℕ → D, Tendsto (f ∘ u) atTop (𝓝 x) := by
    intro x
    have hx : x ∈ closure (Set.range f) := by rw [hf.closure_range]; exact Set.mem_univ x
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hx
    choose u hu using hv
    refine ⟨u, ?_⟩
    have hfu : f ∘ u = v := funext hu
    rw [hfu]
    exact hlim
  choose g hg using hseq

  have hinj : Function.Injective g := by
    intro x y hxy
    have h' : Tendsto (f ∘ g x) atTop (𝓝 y) := by rw [hxy]; exact hg y
    exact tendsto_nhds_unique (hg x) h'
  calc Cardinal.mk X ≤ Cardinal.mk (ℕ → D) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.mk D ^ ℵ₀ := by rw [← Cardinal.mk_nat, Cardinal.power_def]
end ReciprocityTheory.ChartRestriction.T1
