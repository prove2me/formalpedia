-- Prove2me | solution 1 for OddOrder.Peterfalvi.S11.isIndHC_of_source_eq_induce_hcPsiPair
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T12:11:20.525912+00:00
-- url     : https://prove2.me/submissions/024c7384-a75d-443f-9c3c-90d4ef149c4b

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/InnerCompHomBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_InnerCompHomBasic

-- ===== OddOrder/Peterfalvi/S11_MaximalII_III_IV/InnerCompHomBasic.lean =====
namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
/-- **Stages-flattening, pair version**: the `hcPsiPair` analogue of
`isIndHC_of_source_eq_induce_hcPsi`.  A `𝒮`-member whose (irreducible) source equals
`Ind_{HC}^{HU}(hcPsiPair θbar λ)` is induced from a linear character of the `M`-level `HC`
(`HC.map subtype`).  Identical case-split-free tail (`induce_induce_subgroupOf` +
`induce_compHom_subgroupCongr`); the seed is the linear pair character rather than `hcPsi`. -/
theorem _root_.solution [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    [Fintype ↥M] [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)) : ℂ)]
    [Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ)]
    {ζ' : IrreducibleCharacter ↥(huSub data)}
    {θbar : (↥data.H ⧸ chief.N) →* ℂˣ} {lam : ↥(cInHu data chief) →* ℂˣ}
    (hζ'eq : (ζ' : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
          (hcPsiPair chief θbar lam).toClassFunction) :
    ∃ ψ : ClassFunction
        ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      ψ 1 = 1 ∧
      induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ψ := by
  classical
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  let : Fintype ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  have hKle : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype ≤ huSub data :=
    Subgroup.map_subtype_le _
  have hKeq : ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)
      = hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :=
    Subgroup.comap_map_eq_self_of_injective (huSub data).subtype_injective _
  set f : ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype) ≃*
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    (Subgroup.subgroupOfEquivOfLe hKle).symm.trans (MulEquiv.subgroupCongr hKeq) with hf
  refine ⟨ClassFunction.compHom f.toMonoidHom
    (hcPsiPair chief θbar lam : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ),
    ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      f.surjective (hcPsiPair chief θbar lam).isIrreducible
  · rw [ClassFunction.compHom_apply, map_one]
    simp [hcPsiPair]
  · have hstages := OddOrder.RepresentationTheory.induce_induce_subgroupOf
      (M := ↥M) (K := (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)).map (huSub data).subtype) (H := huSub data) hKle
      (ClassFunction.compHom f.toMonoidHom
        (hcPsiPair chief θbar lam : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data)) ℂ))
    have hfe : f.toMonoidHom.comp (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        = (MulEquiv.subgroupCongr hKeq).toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      rw [hf]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    have hcomp : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        (ClassFunction.compHom f.toMonoidHom
          (hcPsiPair chief θbar lam : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ))
        = ClassFunction.compHom (MulEquiv.subgroupCongr hKeq).toMonoidHom
          (hcPsiPair chief θbar lam : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ) := by
      rw [OddOrder.RepresentationTheory.ClassFunction.compHom_comp, hfe]
    have hinner : ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data
        chief).subgroupOf M).subgroupOf (huSub data)).map
          (huSub data).subtype).subgroupOf (huSub data))
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          (ClassFunction.compHom f.toMonoidHom
            (hcPsiPair chief θbar lam : ClassFunction
              ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                (huSub data)) ℂ)))
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsiPair chief θbar lam).toClassFunction := by
      rw [hcomp]
      exact OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKeq _
    calc induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ζ' : ClassFunction ↥(huSub data) ℂ) := by
          unfold induceHU
          congr!
      _ = ClassFunction.induce (huSub data)
            (ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
              M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data))
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
                (ClassFunction.compHom f.toMonoidHom
                  (hcPsiPair chief θbar lam : ClassFunction
                    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                      (huSub data)) ℂ)))) := by rw [hinner, ← hζ'eq]
      _ = _ := hstages

end OddOrder.Peterfalvi.S11
