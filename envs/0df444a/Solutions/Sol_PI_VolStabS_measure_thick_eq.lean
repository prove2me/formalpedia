-- Prove2me | solution 1 for PI.VolStabS.measure_thick_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:56.247429+00:00
-- url     : https://prove2.me/submissions/011ebddc-52e5-474c-9930-62d3a3b8e0fa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_MeasureEqOfCos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Topology Set Filter
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
namespace PI.VolStabS
theorem _root_.solution (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  classical

  have hfib : ∀ c : X ⧸ Λ, m1 (((↑) : X → X ⧸ Λ) ⁻¹' {c}) = m2 (((↑) : X → X ⧸ Λ) ⁻¹' {c}) ∧
      MeasurableSet (((↑) : X → X ⧸ Λ) ⁻¹' {c}) := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    have e : ((↑) : X → X ⧸ Λ) ⁻¹' {(y : X ⧸ Λ)} = {z | z - y ∈ Λ} := by
      ext z
      simp [QuotientAddGroup.eq_iff_sub_mem]
    rw [e]
    exact ⟨h y, (hΛ.preimage (continuous_id.sub continuous_const)).measurableSet⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : S => {z : X | z - (s : X) ∈ Λ})
    (fun s => hΛ.preimage (continuous_id.sub continuous_const))
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, by simp⟩)
  have hT : thick S Λ = ⋃ c ∈ t.image (fun s : S => ((s : X) : X ⧸ Λ)),
      ((↑) : X → X ⧸ Λ) ⁻¹' {c} := by
    ext x
    simp only [thick, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_singleton_iff,
      Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨s', hs't, hss'⟩ := mem_iUnion₂.mp (ht hs)
      refine ⟨((s' : X) : X ⧸ Λ), ⟨s', hs't, rfl⟩, ?_⟩
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have e : x - (s' : X) = (x - s) + (s - s') := by abel
      rw [e]
      exact Λ.add_mem hxs hss'
    · rintro ⟨c, ⟨s', _, rfl⟩, hx⟩
      exact ⟨s', s'.2, (QuotientAddGroup.eq_iff_sub_mem).mp hx⟩
  rw [hT, measure_biUnion_finset, measure_biUnion_finset]
  · exact Finset.sum_congr rfl fun c _ => (hfib c).1
  all_goals first
    | exact fun c _ c' _ hne => (Set.disjoint_singleton.mpr hne).preimage _
    | exact fun c _ => (hfib c).2
end PI.VolStabS
