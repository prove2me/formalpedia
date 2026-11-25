-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.zeroExt_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:13:45.903616+00:00
-- url     : https://prove2.me/submissions/5fb1b822-b384-4c9a-888d-2e6c4f7cc6b4

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveB
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_two_le_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.PLC
variable {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLC
theorem _root_.solution [CompactSpace X] [T2Space X] (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ))
    (v : X → ℝ) (hv : ContDiffOn ℝ ∞ (v ∘ ψ.symm) ψ.target) (hvψ : tsupport v ⊆ ψ.source) :
    ContDiff ℝ 2 (zeroExt ψ v) ∧ HasCompactSupport (zeroExt ψ v) ∧
      (∀ y ∈ ψ.target, zeroExt ψ v =ᶠ[𝓝 y] v ∘ ψ.symm) ∧
      (∀ y ∉ ψ.target, zeroExt ψ v =ᶠ[𝓝 y] 0) := by
  have hK : IsCompact (ψ '' tsupport v) :=
    (isClosed_tsupport v).isCompact.image_of_continuousOn (ψ.continuousOn.mono hvψ)
  have hKt : ψ '' tsupport v ⊆ ψ.target := by
    rintro _ ⟨z, hz, rfl⟩; exact ψ.map_source (hvψ hz)
  have hw0 : ∀ y ∉ ψ '' tsupport v, zeroExt ψ v y = 0 := by
    intro y hy
    unfold zeroExt
    split_ifs with ht
    · exact image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, ψ.right_inv ht⟩
    · rfl
  have hloc1 : ∀ y ∈ ψ.target, zeroExt ψ v =ᶠ[𝓝 y] v ∘ ψ.symm := by
    intro y hy
    filter_upwards [ψ.open_target.mem_nhds hy] with y' hy'
    simp [zeroExt, hy']
  have hloc0 : ∀ y ∉ ψ.target, zeroExt ψ v =ᶠ[𝓝 y] 0 := by
    intro y hy
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds (fun h => hy (hKt h))] with y' hy'
    exact hw0 y' hy'
  refine ⟨?_, HasCompactSupport.intro hK hw0, hloc1, hloc0⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ ψ.target
  · exact ((hv.contDiffAt (ψ.open_target.mem_nhds hy)).of_le two_le_inf).congr_of_eventuallyEq
      (hloc1 y hy)
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hloc0 y hy)
end ReciprocityTheory.AnForm.M.PLC
