-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.thetaWitness_of_caseA
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:08:37.413232+00:00
-- url     : https://prove2.me/submissions/d8d8dd84-0684-485a-8eff-c80722b11c25

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_exists_irreducible_witnessed

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.3.b)-at-`T` caseA — the unconditional branch witness**: in Clifford case (a) a
`ThetaWitness` exists unconditionally.  Mirror of `lambdaWitness_of_caseA`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataT hG hvd chief)) :
    ThetaWitness hyp := by
  classical
  have := hyp.finiteG
  let data := hyp.toTypesIIIIIIVSetupT hG hvd
  let : Fintype ↥hyp.T := Fintype.ofFinite _
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  let : Fintype ↥(hInHu data) := Fintype.ofFinite _
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.T).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.T).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal (data := data) chief
  obtain ⟨θbar, hnt, hreg, hirr⟩ :=
    caseA_exists_irreducible_witnessed (data := data) (chief := chief) caseA hG
  have hθ₀ := caseA_regular_inflation_inertia_eq (data := data) (chief := chief) caseA θbar hreg
  have hζ'mem := hcZeta_mem_xiOf (data := data) chief θbar hnt hθ₀
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsi (M := hyp.T) (data := data) (chief := chief)
      (θbar := θbar)
      (ζ' := ⟨ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.T).subgroupOf (huSub data)) (hcPsi chief θbar),
        hcZeta_irreducible (data := data) chief θbar hθ₀⟩) rfl
  have hwit : induceHU data (ClassFunction.induce (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
      (hcPsi chief θbar).toClassFunction)
      = ClassFunction.induce ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.T).subgroupOf (huSub data)).map (huSub data).subtype) ψ := hψeq
  have hsupeq : (data.H : Subgroup G) ⊔ cSub data chief = hyp.K := by
    rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd,
      hyp.toTypesIIIIIIVSetupT_cSub_eq_D hG hvd chief]
    rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.K.subgroupOf hyp.T := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
      = induceHU data (ClassFunction.induce (hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
        (hcPsi chief θbar).toClassFunction) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hwit]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · intro hker
    have hHUnorm : (huSub data).Normal := by
      rw [huSub_eq_derivedInG_subgroupOf data]; infer_instance
    have hQnorm : (hyp.Q.subgroupOf hyp.T).Normal := by
      have hQle : hyp.Q ≤ hyp.T := by
        rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr ?_
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
    have hQK : hyp.Q.subgroupOf hyp.T ≤ hyp.K.subgroupOf hyp.T :=
      Subgroup.subgroupOf_mono hyp.T (show hyp.Q ≤ hyp.K from le_sup_left)
    have hkerInd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      hQK θ' hker
    have hInd_eq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
        = ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζ'mem.1
    intro x hx
    have hxQ : (x : ↥hyp.T) ∈ hyp.Q.subgroupOf hyp.T := by
      have hx' : x ∈ (data.H.subgroupOf hyp.T).subgroupOf (huSub data) := hx
      rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.T) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction)) := by
      rw [← hInd_eq]; exact hkerInd hxQ
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (hcZeta_irreducible (data := data) chief θbar hθ₀) x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hirr

end OddOrder.Peterfalvi.S15
