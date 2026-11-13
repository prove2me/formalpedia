-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.tSideDadeMap_eq_full_typeP1DadeMap_of_support
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:48.403636+00:00
-- url     : https://prove2.me/submissions/16fb199e-019f-4baa-9b82-93e42b849d2e

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapCross.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapCross.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped BigOperators

/-- Two Peterfalvi (2.2) hypotheses on the same support and subgroup are equal once their
`H`-fields agree.  The `H`-field is the only data field; all other fields are propositions. -/
theorem dadeHypothesis_eq_of_H_eq [Fintype G] {A : Set G} {L : Subgroup G}
    {h₁ h₂ : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    (hH : ∀ a, h₁.H a = h₂.H a) : h₁ = h₂ := by
  obtain ⟨s₁, l₁, n₁, H₁, c₁, ce₁, cd₁, hn₁, cc₁⟩ := h₁
  obtain ⟨s₂, l₂, n₂, H₂, c₂, ce₂, cd₂, hn₂, cc₂⟩ := h₂
  have hHeq : H₁ = H₂ := funext hH
  subst hHeq
  rfl

open scoped Classical in
/-- **Peterfalvi (2.11)/(13.2.e), T-side Dade restriction reconciliation.**

For a type-`P₁` datum on `T`, the Dade map on `A₁(T)=T_σ#` used by the (14.9)
coherent family is the restriction of the full type-`P₁` Dade map on
`A₀(T)=A(T)∪V^T`.  Thus both integral-character lifts agree on every
`A₁(T)`-supported class function.

This is the reusable map-identification step needed before the remaining
`FTtypeP_facts(e)` normed-TI assertion can identify the full map with induction. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    tSideDadeMap hyp hG φ =
      let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
        hG hyp.base.T_maximal dataT hP1).some
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
        (full.dade.fullDadeIsometryData) φ := by
  classical
  let side := (tSideDadeSupport_nonempty hG hyp).some
  let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
    hG hyp.base.T_maximal dataT hP1).some
  have hPA : OddOrder.GroupTheory.typePA hyp.base.T dataT =
      OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    OddOrder.Peterfalvi.S10.typePA_eq_sigmaSharp_of_isTypeP1
      hG hyp.base.T_maximal dataT hP1
  have hA1A0 : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T ⊆
      OddOrder.GroupTheory.typePA0 hyp.base.T dataT := by
    rw [← hPA]
    exact Set.subset_union_left
  have hA1norm : ∀ (l : ↥hyp.base.T) ⦃a : G⦄,
      a ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T →
        (l : G) * a * (l : G)⁻¹ ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    side.dade.L_normalizes_A
  let restricted := full.dade.restrict hA1A0 hA1norm
  have hH : ∀ a, restricted.H a = side.dade.H a := by
    intro a
    rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H,
      full.H_eq_ftSupportKernel, side.H_eq_ftSupportKernel]
    exact (OddOrder.Peterfalvi.S10.ftSupportKernel_restrict hA1A0 a.2).symm
  have hdade : restricted = side.dade := dadeHypothesis_eq_of_H_eq hH
  have hfullSupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T :=
    hφsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA1A0)
  change tSideDadeMap hyp hG φ =
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
      (full.dade.fullDadeIsometryData) φ
  rw [tSideDadeMap,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support side.dade
      (side.dade.fullDadeIsometryData) hφsupp,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support full.dade
      (full.dade.fullDadeIsometryData) hfullSupp]
  rw [← hdade]
  exact full.dade.dadeMap_restrict_apply hA1A0 hA1norm
    ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφsupp⟩

end OddOrder.Peterfalvi.S16
