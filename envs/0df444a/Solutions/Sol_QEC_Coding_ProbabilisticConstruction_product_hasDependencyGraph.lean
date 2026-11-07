-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.product_hasDependencyGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:06.390379+00:00
-- url     : https://prove2.me/submissions/8a2203a1-f280-4784-a7cb-6919a7bc731f

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (ν : ∀ v, Measure (X v))
    [∀ v, IsProbabilityMeasure (ν v)] (vars : I → Finset V)
    (bad : ∀ i, Set (∀ v : vars i, X v)) (hbad : ∀ i, MeasurableSet (bad i)) :
    HasDependencyGraph (Measure.pi ν) (localEvent vars bad) (supportGraph vars) := by
  intro i
  let C : Finset V := (vars i)ᶜ
  have hcoords : iIndepFun (fun v (ω : ∀ v, X v) => ω v) (Measure.pi ν) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hind := hcoords.indepFun_finset (vars i) C (by
    apply Finset.disjoint_left.mpr
    intro v hv hvC
    exact Finset.mem_compl.mp hvC hv)
    (fun v => measurable_pi_apply v)
  apply indep_of_indep_of_le hind
  · apply MeasurableSpace.generateFrom_le
    intro E hE
    have he : E = localEvent vars bad i := Set.mem_singleton_iff.mp hE
    subst E
    exact MeasurableSpace.measurableSet_comap.mpr ⟨bad i, hbad i, rfl⟩
  · apply MeasurableSpace.generateFrom_le
    intro E hE
    obtain ⟨j, hji, hnon, rfl⟩ := hE
    have hdisj : Disjoint (vars i) (vars j) := by
      by_contra h
      exact hnon ⟨Ne.symm hji, h⟩
    have hsub : vars j ⊆ C := by
      intro v hv
      apply Finset.mem_compl.mpr
      intro hvi
      exact Finset.disjoint_left.mp hdisj hvi hv
    refine MeasurableSpace.measurableSet_comap.mpr
      ⟨(Finset.restrict₂ hsub) ⁻¹' bad j,
        (hbad j).preimage (Finset.measurable_restrict₂ hsub), ?_⟩
    rfl
end QEC.Coding.ProbabilisticConstruction
