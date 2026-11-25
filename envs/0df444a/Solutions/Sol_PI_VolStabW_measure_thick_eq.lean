-- Prove2me | solution 1 for PI.VolStabW.measure_thick_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:02:51.253444+00:00
-- url     : https://prove2.me/submissions/dfe556e9-77d5-43a3-ab90-cc068a700bc1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasureEqOfCos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology Set Filter
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
namespace PI.VolStabW
theorem _root_.solution (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  have : DiscreteTopology (X ⧸ Λ) := QuotientAddGroup.discreteTopology hΛ
  let q : X → X ⧸ Λ := QuotientAddGroup.mk
  have hq : Continuous q := continuous_quot_mk
  have hfin : (q '' S).Finite := (hS.image hq).finite_of_discrete
  have hcos : ∀ y, q ⁻¹' {q y} = {z | z - y ∈ Λ} := by
    intro y
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq, q]
    exact QuotientAddGroup.eq_iff_sub_mem
  have hset : thick S Λ = ⋃ p ∈ hfin.toFinset, q ⁻¹' {p} := by
    ext x
    simp only [thick, mem_setOf_eq, mem_iUnion, Finite.mem_toFinset, mem_image, exists_prop]
    constructor
    · rintro ⟨s, hs, hx⟩
      refine ⟨q s, ⟨s, hs, rfl⟩, ?_⟩
      rw [hcos]
      exact hx
    · rintro ⟨p, ⟨s, hs, rfl⟩, hx⟩
      rw [hcos] at hx
      exact ⟨s, hs, hx⟩
  have hmeas : ∀ p : X ⧸ Λ, MeasurableSet (q ⁻¹' {p}) := fun p =>
    ((isOpen_discrete ({p} : Set (X ⧸ Λ))).preimage hq).measurableSet
  have hdisj : PairwiseDisjoint (↑hfin.toFinset : Set (X ⧸ Λ)) (fun p => q ⁻¹' {p}) :=
    fun p _ p' _ hne => (disjoint_singleton.2 hne).preimage q
  rw [hset, measure_biUnion_finset hdisj (fun p _ => hmeas p),
    measure_biUnion_finset hdisj (fun p _ => hmeas p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective p
  have := hcos y
  simp only [q] at this
  rw [this]
  exact h y
end PI.VolStabW
