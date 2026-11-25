-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.contDiff_chartExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:07:03.689288+00:00
-- url     : https://prove2.me/submissions/3eb38673-82e3-4aca-a9ae-40ce4ebbaf32

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiffOn_compat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution [T2Space X] [CompactSpace X] {A : FinHolAtlas e X}
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {v : X → ℝ}
    (hv : A.Smooth v) (hvs : tsupport v ⊆ ψ.source) :
    ContDiff ℝ ∞ (chartExt ψ v) ∧ IsCompact (ψ '' tsupport v) ∧
      tsupport (chartExt ψ v) ⊆ ψ '' tsupport v := by
  have hK : IsCompact (ψ '' tsupport v) :=
    (isClosed_tsupport v).isCompact.image_of_continuousOn (ψ.continuousOn.mono hvs)
  have hsupp : ∀ y, y ∉ ψ '' tsupport v → chartExt ψ v y = 0 := by
    intro y hy
    unfold chartExt
    by_cases ht : y ∈ ψ.target
    · rw [Set.indicator_of_mem ht]
      by_contra hne
      exact hy ⟨ψ.symm y, subset_tsupport _ hne, ψ.right_inv ht⟩
    · exact Set.indicator_of_notMem ht _
  refine ⟨?_, hK, closure_minimal (fun y hy => by_contra fun h => hy (hsupp y h)) hK.isClosed⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases ht : y ∈ ψ.target
  · have h1 := contDiffOn_compat hψ isOpen_univ hv
    simp only [Set.preimage_univ, Set.inter_univ] at h1
    refine (h1.contDiffAt (ψ.open_target.mem_nhds ht)).congr_of_eventuallyEq ?_
    filter_upwards [ψ.open_target.mem_nhds ht] with y' hy'
    simp [chartExt, Set.indicator_of_mem hy']
  · have hy : y ∉ ψ '' tsupport v := by
      rintro ⟨p, hp, rfl⟩; exact ht (ψ.map_source (hvs hp))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hy] with y' hy'
    exact hsupp y' hy'
end ReciprocityTheory.AnForm.M.PLAux
