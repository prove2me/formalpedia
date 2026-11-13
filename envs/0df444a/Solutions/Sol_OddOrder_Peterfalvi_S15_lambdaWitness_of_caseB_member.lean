-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.lambdaWitness_of_caseB_member
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:20.298466+00:00
-- url     : https://prove2.me/submissions/8a1c0a95-c45a-463e-b2af-d2882fb156fe

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
/-- **(13.3.b) caseB forward — the Singer/Galois branch witness**: an irreducible member `χ` of
the `S`-instance family `𝒮(H₀ ⊔ C')` in Clifford case (b) is a `LambdaWitness` (a `uq`-degree
`PC`-linear induced irreducible).  Mirrors the caseA branch of `S_caseB_facts_no_lambda` (which
produces the witness unconditionally from the (9.8.c) regular seed); here the source is the given
`χ = Ind_{HU} ζ`, and the reverse (13.3.a)-for-irr characterization is the pair (`C'`-kernel)
`caseB_xiOf_H0Cprime_eq_induce_hcPsiPair`: `ζ ∈ 𝒳(H₀C')` irreducible equals
`Ind_{HC}(hcPsiPair θ̄ λ)` for a linear pair character (`λ` trivial on `C'`).  Flattening
(`isIndHC_of_source_eq_induce_hcPsiPair`) and the `HC.map subtype = (PC).subgroupOf S` transport
(`hcRealized_map_subtype_eq`, `toTypesIIIIIIVSetupS_cSub_eq_C`) give the linear
`θ' ∈ Irr(H.subgroupOf S)` with `P ⊄ Ker θ'` whose induction (`= χ`) is irreducible.

Stated with `chief`/`caseB`/`χ`-membership as explicit arguments (no `set` inside): the caseB
branch of `S_caseB_facts_no_lambda` is then a one-line call. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData (hyp.mkSection11CharacterDataS hG chief))
    {χ : ClassFunction ↥hyp.S ℂ}
    (hχmem : χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime))
    (_hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    LambdaWitness hyp := by
  classical
  have := hyp.finiteG
  -- Extract the source `ζ ∈ 𝒳(H₀C')` of the given irreducible `χ = Ind_{HU} ζ`.  Done *before*
  -- any `let`, and re-cast to `data`-form so every downstream term is uniform (a `set` here would
  -- revert/rename `ζ`; the extraction stays clean because `hχmem` names the explicit terms).
  rw [Section11CharacterData.SOf_eq] at hχmem
  let data := hyp.toTypesIIIIIIVSetupS hG
  have hχmem' : χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := hχmem
  obtain ⟨ζ, hζxi, hχeq⟩ := mem_sOf.mp hχmem'
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
  -- (1) the reverse (13.3.a)-for-irr characterization: `ζ = Ind_{HC}(hcPsiPair θ̄ λ)`, `θ̄ ≠ 1`.
  obtain ⟨θbar, lam, hnt, hlamC', hζeq⟩ :=
    caseB_xiOf_H0Cprime_eq_induce_hcPsiPair (data := data) (chief := chief) caseB hζxi
  -- (2) flatten `induceHU(Ind_{HC}(hcPsiPair)) = Ind_{HC.map subtype}(ψ)`, `ψ` linear irr.
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsiPair (M := hyp.S) (data := data) (chief := chief)
      (θbar := θbar) (lam := lam) (ζ' := ζ) hζeq
  -- (3) transport `HC.map subtype = (PC).subgroupOf S`.
  have hHeq : data.H = hyp.P := by change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hsupeq : data.H ⊔ cSub data chief = hyp.H := by
    rw [hHeq, hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]; rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.H.subgroupOf hyp.S := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
      = induceHU data (ζ : ClassFunction ↥(huSub data) ℂ) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hψeq]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · -- `P ⊄ Ker θ'`: else `P ⊆ Ker(Ind θ') = Ker(Ind_{HU} ζ)`, which (converse (1.6.a)) pushes to
    -- `P ⊆ Ker ζ`, contradicting `ζ ∈ 𝒳` (`P = H ⊄ Ker ζ`).  Mirrors `mu_j_isIndPC_not_ker`.
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
        = ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζxi.1
    intro x hx
    have hxP : (x : ↥hyp.S) ∈ hyp.P.subgroupOf hyp.S := by
      have hx' : x ∈ (data.H.subgroupOf hyp.S).subgroupOf (huSub data) := hx
      rw [hHeq] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.S) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ)) := by
      rw [← hInd_eq]; exact hkerInd hxP
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      ζ.isIrreducible x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hχeq ▸ _hχirr

end OddOrder.Peterfalvi.S15
