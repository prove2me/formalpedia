-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.thetaWitness_of_caseB_member
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:45.586288+00:00
-- url     : https://prove2.me/submissions/db1459d0-e1a5-47d7-8446-6389f4ca4fdb

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
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply
import Theorems.Thm_OddOrder_Peterfalvi_S11_caseB_xiOf_H0Cprime_eq_induce_hcPsiPair
import Theorems.Thm_OddOrder_Peterfalvi_S11_isIndHC_of_source_eq_induce_hcPsiPair

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.3.b)-at-`T` caseB forward — the Singer/Galois branch witness**: an irreducible
member `χ` of the `T`-instance family `𝒮_T(H₀ ⊔ C')` in Clifford case (b) is a
`ThetaWitness`.  Mirror of `lambdaWitness_of_caseB_member`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataT hG hvd chief))
    {χ : ClassFunction ↥hyp.T ℂ}
    (hχmem : χ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime))
    (_hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    ThetaWitness hyp := by
  classical
  have := hyp.finiteG
  rw [Section11CharacterData.SOf_eq] at hχmem
  let data := hyp.toTypesIIIIIIVSetupT hG hvd
  have hχmem' : χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := hχmem
  obtain ⟨ζ, hζxi, hχeq⟩ := mem_sOf.mp hχmem'
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
  obtain ⟨θbar, lam, hnt, hlamC', hζeq⟩ :=
    caseB_xiOf_H0Cprime_eq_induce_hcPsiPair (data := data) (chief := chief) caseB hζxi
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsiPair (M := hyp.T) (data := data) (chief := chief)
      (θbar := θbar) (lam := lam) (ζ' := ζ) hζeq
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
      = induceHU data (ζ : ClassFunction ↥(huSub data) ℂ) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hψeq]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · -- `Q ⊄ Ker θ'`: else `Q ⊆ Ker(Ind θ') = Ker(Ind_{HU} ζ)` pushes to `Q ⊆ Ker ζ`,
    -- contradicting `ζ ∈ 𝒳` (`Q = H ⊄ Ker ζ`).
    intro hker
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
        = ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζxi.1
    intro x hx
    have hxQ : (x : ↥hyp.T) ∈ hyp.Q.subgroupOf hyp.T := by
      have hx' : x ∈ (data.H.subgroupOf hyp.T).subgroupOf (huSub data) := hx
      rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.T) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ)) := by
      rw [← hInd_eq]; exact hkerInd hxQ
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      ζ.isIrreducible x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hχeq ▸ _hχirr

end OddOrder.Peterfalvi.S15
