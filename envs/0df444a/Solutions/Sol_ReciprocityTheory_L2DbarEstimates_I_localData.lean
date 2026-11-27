-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.localData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:02.680686+00:00
-- url     : https://prove2.me/submissions/703bbb4e-fc16-4664-8511-06c19cb638cb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocallyCompactSpaceOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_holo_continuous_of_isLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_locallyCompactSpace_of_isLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ev_pos_of_not_mem_zeroSet
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] : LocalStatement n M := by
  intro z g ph r N hz hg hph hr hS _hJ hN
  have := locallyCompactSpace_of_isLocalHomeomorph n z hz
  obtain ⟨U, hU, hUd⟩ := hS.t2_separation
  have hex : ∀ p ∈ zeroSet n g, ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ closure V ⊆ N p ∩ U p ∧
      IsCompact (closure V) := by
    intro p hp
    obtain ⟨V, hVo, hpV, hcl, hcpt⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := p)) ((hN p hp).1.inter (hU p).2)
      (Set.singleton_subset_iff.mpr ⟨(hN p hp).2, (hU p).1⟩)
    exact ⟨V, hVo, hpV (Set.mem_singleton p), hcl, hcpt⟩
  choose! W hWo hpW hWcl hWc using hex
  have hgc : ∀ i, Continuous (g i) := fun i =>
    holo_continuous_of_isLocalHomeomorph n z hz _ (hg i)
  have hphc : Continuous ph :=
    (Complex.continuous_re.comp (Smooth.continuous n z hz _ hph)).congr (fun x => by simp)
  have hevc : Continuous (ev n g ph r) := by
    unfold ev
    fun_prop
  have hfr : ∀ p ∈ zeroSet n g, ∀ x ∈ frontier (W p), x ∉ zeroSet n g := by
    intro p hp x hx hxS
    have hxU : x ∈ U p := (hWcl p hp (frontier_subset_closure hx)).2
    by_cases hxp : x = p
    · rw [hxp, (hWo p hp).frontier_eq] at hx
      exact hx.2 (hpW p hp)
    · exact Set.disjoint_left.mp (hUd hxS hp hxp) (hU x).1 hxU
  have hK : IsCompact (⋃ p ∈ zeroSet n g, frontier (W p)) :=
    hS.isCompact_biUnion fun p hp =>
      (hWc p hp).of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hpos : ∀ x ∈ ⋃ p ∈ zeroSet n g, frontier (W p), 0 < ev n g ph r x := by
    intro x hx
    obtain ⟨p, hp, hxf⟩ := Set.mem_iUnion₂.mp hx
    exact ev_pos_of_not_mem_zeroSet n g ph r hr x (hfr p hp x hxf)
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' hevc.continuousOn hpos
  refine ⟨W, m, ⟨hm, fun p hp => ⟨hWo p hp, hpW p hp, hWc p hp,
    fun x hx => hmK x (Set.mem_biUnion hp hx), fun q hq hqp => ?_⟩⟩,
    fun p hp x hx => (hWcl p hp (subset_closure hx)).1⟩
  exact Disjoint.mono (fun x hx => (hWcl p hp hx).2) (fun x hx => (hWcl q hq hx).2)
    (hUd hp hq hqp.symm)
end ReciprocityTheory.L2DbarEstimates.I
