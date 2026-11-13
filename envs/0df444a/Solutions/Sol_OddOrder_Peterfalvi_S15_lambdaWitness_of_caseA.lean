-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.lambdaWitness_of_caseA
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:08:38.824104+00:00
-- url     : https://prove2.me/submissions/daa3c397-5eba-41e3-85ff-59c6c15d70cc

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
/-- **(13.3.b) caseA — the unconditional branch witness**: in Clifford case (a) a `LambdaWitness`
exists unconditionally (independent of the given `χ`).  The (9.8.c) degree-`qu` irreducible member
`Ind_{HU}^S(Ind_{HC}(hcPsi θ̄))` for a *regular* seed `θ̄` (`caseA_exists_irreducible_witnessed`) is
`Ind_{PC}^S(linear irr)`: flattening (`isIndHC_of_source_eq_induce_hcPsi`) and the
`HC.map subtype = (PC).subgroupOf S` transport give the linear `θ' ∈ Irr(H.subgroupOf S)` with
`P ⊄ Ker θ'` whose induction is irreducible.

Stated with `chief`/`caseA` explicit (no `set` inside), so the caseA branch of
`S_caseB_facts_no_lambda` is a one-line call and hbridge stays `set`-free (a `set` there would
split `chief` and desync the branch calls). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData (hyp.mkSection11CharacterDataS hG chief)) :
    LambdaWitness hyp := by
  classical
  have := hyp.finiteG
  let data := hyp.toTypesIIIIIIVSetupS hG
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  let : Fintype ↥(hInHu data) := Fintype.ofFinite _
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.S).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.S).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal (data := data) chief
  -- (1) the regular seed `θbar` with irreducible `induceHU(Ind_{HC}(hcPsi θbar))`.
  obtain ⟨θbar, hnt, hreg, hirr⟩ :=
    caseA_exists_irreducible_witnessed (data := data) (chief := chief) caseA hG
  have hθ₀ := caseA_regular_inflation_inertia_eq (data := data) (chief := chief) caseA θbar hreg
  -- (2) the `S'`-source `ζ' = Ind_{HC}(hcPsi θbar) ∈ 𝒳(H₀C)` (`P ⊄ Ker ζ'`).
  have hζ'mem := hcZeta_mem_xiOf (data := data) chief θbar hnt hθ₀
  -- (3) flatten `induceHU(Ind_{HC}(hcPsi)) = Ind_{HC.map subtype}(ψ)`, `ψ` linear irr.
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsi (M := hyp.S) (data := data) (chief := chief)
      (θbar := θbar)
      (ζ' := ⟨ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.S).subgroupOf (huSub data)) (hcPsi chief θbar),
        hcZeta_irreducible (data := data) chief θbar hθ₀⟩) rfl
  have hwit : induceHU data (ClassFunction.induce (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
      (hcPsi chief θbar).toClassFunction)
      = ClassFunction.induce ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.S).subgroupOf (huSub data)).map (huSub data).subtype) ψ := hψeq
  -- (4) transport `HC.map subtype = (PC).subgroupOf S`.
  have hHeq : data.H = hyp.P := by change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hsupeq : data.H ⊔ cSub data chief = hyp.H := by
    rw [hHeq, hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]; rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.H.subgroupOf hyp.S := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
      = induceHU data (ClassFunction.induce (hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
        (hcPsi chief θbar).toClassFunction) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hwit]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · -- `P ⊄ Ker θ'`: else `P ⊆ Ker(Ind θ') = Ker(Ind_{HU} ζ')` pushes to `P ⊆ Ker ζ'`,
    -- contradicting `ζ' ∈ 𝒳` (`P = H ⊄ Ker ζ'`).  Mirrors `mu_j_isIndPC_not_ker`.
    intro hker
    have hHUnorm : (huSub data).Normal := by
      rw [huSub_eq_derivedInG_subgroupOf data]; infer_instance
    have hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
      have hPle : hyp.P ≤ hyp.S := by
        rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr ?_
      rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    have hPH : hyp.P.subgroupOf hyp.S ≤ hyp.H.subgroupOf hyp.S :=
      Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
    have hkerInd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      hPH θ' hker
    have hInd_eq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
        = ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζ'mem.1
    intro x hx
    have hxP : (x : ↥hyp.S) ∈ hyp.P.subgroupOf hyp.S := by
      have hx' : x ∈ (data.H.subgroupOf hyp.S).subgroupOf (huSub data) := hx
      rw [hHeq] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.S) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction)) := by
      rw [← hInd_eq]; exact hkerInd hxP
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (hcZeta_irreducible (data := data) chief θbar hθ₀) x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hirr

end OddOrder.Peterfalvi.S15
