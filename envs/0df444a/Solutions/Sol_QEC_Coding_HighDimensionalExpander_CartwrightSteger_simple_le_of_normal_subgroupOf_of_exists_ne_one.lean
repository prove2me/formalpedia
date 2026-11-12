-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.simple_le_of_normal_subgroupOf_of_exists_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:49:23.828191+00:00
-- url     : https://prove2.me/submissions/1425ac5f-87db-4d15-89b5-0db99f1206b7

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    {G : Type*} [Group G]
    (S H A : Subgroup G) [IsSimpleGroup S]
    (hSA : S ≤ A)
    [((H.subgroupOf A)).Normal]
    (hne : ∃ g : G, g ∈ H ∧ g ∈ S ∧ g ≠ 1) :
    S ≤ H := by
  let N : Subgroup S := H.comap S.subtype
  have hNnormal : N.Normal := by
    constructor
    intro n hn s
    change (s : G) * (n : G) * (s : G)⁻¹ ∈ H
    have hnA : (n : G) ∈ A := hSA n.property
    have hsA : (s : G) ∈ A := hSA s.property
    have hnH : (n : G) ∈ H := hn
    let nA : A := ⟨n, hnA⟩
    let sA : A := ⟨s, hsA⟩
    have hnSub : nA ∈ H.subgroupOf A := hnH
    have hconj := (inferInstance : (H.subgroupOf A).Normal).conj_mem
      nA hnSub sA
    exact hconj
  obtain ⟨g, hgH, hgS, hg1⟩ := hne
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hgN : (⟨g, hgS⟩ : S) ∈ N := hgH
    rw [hbot, Subgroup.mem_bot] at hgN
    exact hg1 (congrArg Subtype.val hgN)
  have hNtop : N = ⊤ :=
    hNnormal.eq_bot_or_eq_top.resolve_left hNne
  intro s hs
  have hsN : (⟨s, hs⟩ : S) ∈ N := by
    rw [hNtop]
    exact Subgroup.mem_top _
  exact hsN
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
