-- Prove2me | solution 1 for PI.VolStabSW.measure_thick_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:58:20.126712+00:00
-- url     : https://prove2.me/submissions/41d67a2f-858a-4f20-84fa-8a34e91c92aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasureEqOfCos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology Set Filter
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
namespace PI.VolStabSW
theorem _root_.solution (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  classical
  have hC : ∀ y, IsOpen {z : X | z - y ∈ Λ} := fun y =>
    hΛ.preimage (continuous_id.sub continuous_const)
  have hfin : ∀ t : Finset X,
      m1 (⋃ s ∈ t, {z | z - s ∈ Λ}) = m2 (⋃ s ∈ t, {z | z - s ∈ Λ}) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert s0 t hs0 ih =>
      rw [Finset.set_biUnion_insert]
      by_cases hex : ∃ s ∈ t, s0 - s ∈ Λ
      · obtain ⟨s, hs, hss⟩ := hex
        have hsub : {z : X | z - s0 ∈ Λ} ⊆ ⋃ s ∈ t, {z | z - s ∈ Λ} := by
          intro z hz
          simp only [Set.mem_iUnion, Set.mem_setOf_eq]
          exact ⟨s, hs, by simpa [sub_add_sub_cancel] using Λ.add_mem hz hss⟩
        rw [Set.union_eq_right.2 hsub, ih]
      · push_neg at hex
        have hdisj : Disjoint {z : X | z - s0 ∈ Λ} (⋃ s ∈ t, {z | z - s ∈ Λ}) := by
          rw [Set.disjoint_left]
          intro z hz hz'
          simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz'
          obtain ⟨s, hs, hzs⟩ := hz'
          apply hex s hs
          simpa [sub_sub_sub_cancel_left] using Λ.sub_mem hzs hz
        have hmeas : MeasurableSet (⋃ s ∈ t, {z : X | z - s ∈ Λ}) :=
          (isOpen_biUnion fun s _ => hC s).measurableSet
        rw [measure_union hdisj hmeas, measure_union hdisj hmeas, h, ih]
  obtain ⟨t, htS, hcov⟩ := hS.elim_nhds_subcover (fun x => {z : X | z - x ∈ Λ})
    (fun x _ => (hC x).mem_nhds (by simp [Λ.zero_mem]))
  have heq : thick S Λ = ⋃ s ∈ t, {z : X | z - s ∈ Λ} := by
    ext x
    simp only [thick, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨u, hu, hsu⟩ := Set.mem_iUnion₂.1 (hcov hs)
      exact ⟨u, hu, by simpa [sub_add_sub_cancel] using Λ.add_mem hxs hsu⟩
    · rintro ⟨u, hu, hxu⟩
      exact ⟨u, htS u hu, hxu⟩
  rw [heq]
  exact hfin t
end PI.VolStabSW
