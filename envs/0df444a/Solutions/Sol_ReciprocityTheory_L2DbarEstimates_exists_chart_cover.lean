-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.exists_chart_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:25.557684+00:00
-- url     : https://prove2.me/submissions/03d916fd-6950-4145-93ce-728352ee4f0b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) :
    ∃ T : ℕ → Set M, (∀ i, IsOpen (T i)) ∧ (⋃ i, T i = univ) ∧
      ∀ i, T i = ∅ ∨ ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ T i ⊆ e.source := by
  classical
  have hz' : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), x ∈ e.source ∧ z = e := hz
  choose e hxe hze using hz'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x => (e x).source)
    (fun x => (e x).open_source)
  have hmem : ∀ x, x ∈ ⋃ y ∈ T, (e y).source := by
    intro x; rw [hTU]; exact Set.mem_iUnion.2 ⟨x, hxe x⟩
  by_cases hT : T.Nonempty
  · obtain ⟨g, hg⟩ := hTc.exists_eq_range hT
    refine ⟨fun i => (e (g i)).source, fun i => (e (g i)).open_source, ?_,
      fun i => Or.inr ⟨e (g i), fun w _ => congrFun (hze (g i)) w, subset_rfl⟩⟩
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨y, hyT, hy⟩ := Set.mem_iUnion₂.1 (hmem x)
    rw [hg] at hyT
    obtain ⟨i, rfl⟩ := hyT
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  · refine ⟨fun _ => ∅, fun _ => isOpen_empty, ?_, fun _ => Or.inl rfl⟩
    rw [Set.not_nonempty_iff_eq_empty] at hT
    ext x
    exfalso
    have h1 := hmem x
    rw [hT] at h1
    simp at h1
end ReciprocityTheory.L2DbarEstimates
