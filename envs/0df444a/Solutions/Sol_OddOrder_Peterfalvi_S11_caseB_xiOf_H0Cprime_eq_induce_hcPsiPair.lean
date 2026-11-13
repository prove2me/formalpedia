-- Prove2me | solution 1 for OddOrder.Peterfalvi.S11.caseB_xiOf_H0Cprime_eq_induce_hcPsiPair
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T12:06:53.739362+00:00
-- url     : https://prove2.me/submissions/18779f20-2cfc-46c8-991c-30ec5b1fd016

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
/-- **Case-(b) pair exhaustion of `𝒳(H₀C')`** (the `C'`-kernel analogue of
`caseB_xiOf_H0C_eq_induce_hcPsi`): every `ζ ∈ 𝒳(H₀C')` equals `Ind_{HC}^{HU}(hcPsiPair θ λ)` for a
nontrivial seed `θ : H̄ →* ℂˣ` and a linear `λ : C →* ℂˣ` trivial on `C'`.

Factors a constituent `ψ` of `Res_{HC} ζ` *not* killing `H`
(`exists_constituent_not_subset_characterKernel`, from `ζ ∈ 𝒳`).  `ψ` is linear
(`[HC,HC] ⊆ H₀C' ⊆ Ker ζ ⟹ Ker ψ`, `commutator_hcInHu_le_realized`); its `C`-restriction is `λ`
(trivial on `C'` since `C' ⊆ H₀C'`), and the correction `φ = ψ·(λ-lift)⁻¹` kills `H₀C`
(`realizedH0supC_eq_realizedH0_sup_cInHu`), so `φ = θ ∘ hcHom` factors through the chief factor
(`exists_compHom_eq_of_subset_characterKernel`), giving `ψ = hcPsiPair θ λ`.  `H ⊄ Ker ψ` forces
`θ ≠ 1`, so the case-(b) inertia `inertia(hcPsiPair θ λ) = HC` (`hcPsiPair_inertia_eq_hc` via
`inertia_eq_hcInHu`) makes `Ind_{HC}(hcPsiPair θ λ)` irreducible and the Clifford correspondence
(`coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce`) yields
`ζ = Ind_{HC}(hcPsiPair θ λ)`. -/
theorem _root_.solution [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseB : CliffordCaseBData chars)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    {ζ : IrreducibleCharacter ↥(huSub data)}
    (hζ : ζ ∈ xiOf data (chief.H0 ⊔ cprimeSub data chief)) :
    ∃ (θbar : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ), θbar ≠ 1 ∧
      (∀ c : ↥(cInHu data chief),
        (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
        lam c = 1) ∧
      (ζ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsiPair chief θbar lam).toClassFunction := by
  classical
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype (IrreducibleCharacter ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data))) := Fintype.ofFinite _
  have hNC := realizedH0supC_normal_huSub chief
  have : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    hNC.subgroupOf _
  obtain ⟨hζX, hζK⟩ := hζ
  -- (1) A constituent `ψ` of `Res_{HC} ζ` not killing `H` (`ζ ∈ 𝒳`, so `H ⊄ Ker ζ`).
  obtain ⟨ψ, hψover, hψnt⟩ :=
    OddOrder.RepresentationTheory.exists_constituent_not_subset_characterKernel
      (A := hInHu data)
      (B := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      le_sup_left ζ hζX
  -- (2) `ψ` kills `H₀C'` (from `H₀C' ⊆ Ker ζ` and lies-over kernel inheritance).
  have hψkerC' : ∀ x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)),
      (x : ↥(huSub data)) ∈ ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf
        (huSub data) →
      x ∈ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
    intro x hx
    exact liesOver_mem_characterKernel hψover (hζK hx)
  -- (3) `ψ` is linear: `[HC,HC] ⊆ H₀C' ⊆ Ker ζ ⊆ Ker ψ`.
  have hψ1 : (ψ : ClassFunction ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) ℂ) 1 = 1 := by
    have : IsMulCommutative (↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) ⧸ commutator ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data
        chief).subgroupOf M).subgroupOf (huSub data))) :=
      inferInstanceAs (IsMulCommutative (Abelianization _))
    refine apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := commutator ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data))) ψ ?_
    intro g hg
    apply hψkerC'
    have hcomm : ⁅hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data),
        hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)⁆
        ≤ ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) := by
      rw [hInHu_sup_realizedH0supC chief]
      exact commutator_hcInHu_le_realized data chief
    apply hcomm
    rw [← derivedInG_eq_commutator]
    exact Subgroup.mem_map_of_mem _ hg
  -- (4) The underlying hom `ψhom` of the linear `ψ`, and `λ = ψhom|_C`.
  obtain ⟨ψhom, hψhom⟩ :=
    ψ.isIrreducible.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one hψ1
  set lam : ↥(cInHu data chief) →* ℂˣ :=
    ψhom.comp (Subgroup.inclusion (cInHu_le_hcRealized chief)) with hlamdef
  -- `ψhom = 1` on any `x ∈ HC` in `Ker ψ`.
  have hψhom_one : ∀ x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)),
      x ∈ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) →
      ψhom x = 1 := by
    intro x hx
    have hval : (ψ : ClassFunction ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) ℂ) x = 1 := by
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hx
      rw [hx]; exact hψ1
    have h2 : (ψhom x : ℂ) = 1 := by rw [← linearIrreducibleCharacter_apply ψhom, hψhom]; exact hval
    exact Units.val_eq_one.mp h2
  -- (5) `λ` kills `C'` (`C' ⊆ H₀C' ⊆ Ker ψ`).
  have hlam : ∀ c : ↥(cInHu data chief),
      (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1 := by
    intro c hc
    rw [hlamdef, MonoidHom.comp_apply]
    refine hψhom_one _ (hψkerC' _ ?_)
    rw [Subgroup.coe_inclusion]
    exact (Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M le_sup_right)) hc
  -- (6) `φ = ψhom · (hcLambdaHom λ)⁻¹` factors through `hcHom` (`φ` kills `H₀C`).
  set φ : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) →*
      ℂˣ :=
    ψhom * (hcLambdaHom chief lam)⁻¹ with hφdef
  have hφkerH0 : ((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ≤
        φ.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hxH : x ∈ (hInHu data).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) := by
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M chief.H0_lt_H.le)) hx
    rw [MonoidHom.mem_ker, hφdef, MonoidHom.mul_apply, MonoidHom.inv_apply,
      hcLambdaHom_eq_one_of_mem_hInHu chief lam hxH, inv_one, mul_one]
    exact hψhom_one x (hψkerC' x
      ((Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M le_sup_left)) hx))
  have hφkerC : (cInHu data chief).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ≤
        φ.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hxc : x = Subgroup.inclusion (cInHu_le_hcRealized chief)
        (⟨(x : ↥(huSub data)), hx⟩ : ↥(cInHu data chief)) :=
      Subtype.ext (by rw [Subgroup.coe_inclusion])
    rw [MonoidHom.mem_ker, hxc, hφdef, MonoidHom.mul_apply, MonoidHom.inv_apply,
      hcLambdaHom_inclusion chief lam, hlamdef, MonoidHom.comp_apply, mul_inv_cancel]
  have hH0leHC : (chief.H0.subgroupOf M).subgroupOf (huSub data)
      ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :=
    le_trans (Subgroup.subgroupOf_mono (huSub data)
      (Subgroup.subgroupOf_mono M chief.H0_lt_H.le)) le_sup_left
  have hφkerH0C : (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ≤ φ.ker :=
    calc (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        ≤ (((chief.H0.subgroupOf M).subgroupOf (huSub data)) ⊔ cInHu data chief).subgroupOf
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
          Subgroup.subgroupOf_mono _ (realizedH0supC_eq_realizedH0_sup_cInHu chief).le
      _ = ((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
          ⊔ (cInHu data chief).subgroupOf
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
          Subgroup.subgroupOf_sup hH0leHC (cInHu_le_hcRealized chief)
      _ ≤ φ.ker := sup_le hφkerH0 hφkerC
  -- factor `φ = θ ∘ hcHom` at character level (through the chief factor `hcHom`).
  have hkerφ : ((hcHom chief).ker : Set ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (linearIrreducibleCharacter φ : ClassFunction
          ↥(hInHu data ⊔
            ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
    intro x hx
    have hx1 : hcHom chief x = 1 := hx
    have hxH0C : x ∈ (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) := by
      rw [hcHom, MonoidHom.comp_apply] at hx1
      have h2 : (QuotientGroup.mk' ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) x)
          = 1 := by
        apply (hcQuotientEquivHbar chief).injective
        rw [map_one]; exact hx1
      rw [QuotientGroup.mk'_apply] at h2
      exact (QuotientGroup.eq_one_iff x).mp h2
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
      linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply_one,
      MonoidHom.mem_ker.mp (hφkerH0C hxH0C), Units.val_one]
  obtain ⟨θbarChar, hθbarChar⟩ :=
    OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel
      (hcHom_surjective chief) (linearIrreducibleCharacter φ) hkerφ
  have : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  obtain ⟨θbar, hθbar⟩ :=
    θbarChar.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  -- `θbar ∘ hcHom = φ`.
  have hφfac : θbar.comp (hcHom chief) = φ := by
    apply linearIrreducibleCharacter_injective
    apply IrreducibleCharacter.ext
    rw [← ClassFunction.compHom_linearIrreducibleCharacter, hθbar, hθbarChar]
  -- `ψhom = hcPairHom θbar λ`, hence `ψ = hcPsiPair θbar λ`.
  have hψhomeq : ψhom = hcPairHom chief θbar lam := by
    have hunfold : hcPairHom chief θbar lam
        = θbar.comp (hcHom chief) * hcLambdaHom chief lam := rfl
    rw [hunfold, hφfac, hφdef]
    exact (inv_mul_cancel_right ψhom (hcLambdaHom chief lam)).symm
  have hψeq' : ψ = hcPsiPair chief θbar lam := by
    apply IrreducibleCharacter.ext
    rw [← hψhom, hcPsiPair, hψhomeq]
  -- (7) `θbar ≠ 1` (else `ψ|_H = 1`, contradicting `H ⊄ Ker ψ`).
  have hθne : θbar ≠ 1 := by
    intro h1
    apply hψnt
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    have hxh : x = Subgroup.inclusion le_sup_left (⟨(x : ↥(huSub data)), hx⟩ : ↥(hInHu data)) :=
      Subtype.ext (by rw [Subgroup.coe_inclusion])
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    have hval : (ψ : ClassFunction ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) ℂ) x = 1 := by
      rw [hxh, hψeq', hcPsiPair_apply_inclusion chief θbar lam, h1]
      simp [ClassFunction.compHom_apply]
    rw [hval, hψ1]
  -- (8) inertia `= HC`, `Ind` irreducible, Clifford correspondence.
  have hθbarnt : (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      ≠ trivialClassFunction _ := by
    intro h0
    apply hθne
    rw [← linearIrreducibleCharacter_eq_trivial_iff]
    exact IrreducibleCharacter.ext
      (h0.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm)
  have hθ₀ := inertia_eq_hcInHu data chief caseB.actsIrreducibly hθbarnt
  refine ⟨θbar, lam, hθne, hlam, ?_⟩
  exact OddOrder.RepresentationTheory.coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce
    (G := ↥(huSub data)) ζ (hcPsiPair chief θbar lam)
    (hcZetaPair_irreducible chief θbar lam hθ₀) (hψeq' ▸ hψover)

end OddOrder.Peterfalvi.S11
