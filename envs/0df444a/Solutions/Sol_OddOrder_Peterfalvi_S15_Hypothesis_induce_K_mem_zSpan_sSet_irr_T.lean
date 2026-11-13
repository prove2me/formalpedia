-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.induce_K_mem_zSpan_sSet_irr_T
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:56:01.222199+00:00
-- url     : https://prove2.me/submissions/5d8c0f79-06ac-46cf-98bd-f32189128d09

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/ChiefFactorBasic.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean
--   OddOrder/Peterfalvi/S15_CaseACoherence.lean
--   OddOrder/Peterfalvi/S15_Tau1T.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_Tau1T

-- ===== OddOrder/Peterfalvi/S11_MaximalII_III_IV/ChiefFactorBasic.lean =====
namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

theorem mem_sSet [Finite G] {data : TypesIIIIIIVSetup M} {φ : ClassFunction ↥M ℂ} :
    φ ∈ sSet data ↔ ∃ χ ∈ xiSet data, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) :=
  Iff.rfl

end OddOrder.Peterfalvi.S11

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **`K = QD ⊴ T`** (as `K.subgroupOf T`): `Q = T_F ⊴ T` (Fitting Hall) and `D = V ⊓ C_G(Q)`
is `T`-normalized (`typePData_C_normalized_by_M` on the reconciled datum — `D` is the
`π(Q)'`-part of `F(T)`), so the join is normal.  The support engine of the (13.4) θ-package:
characters induced from the normal `K` vanish off `K`. -/
theorem Hypothesis.K_subgroupOf_T_normal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : (hyp.K.subgroupOf hyp.T).Normal := by
  have := hyp.finiteG
  obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
  have hUne : tpd.U ≠ ⊥ := by
    intro hbot
    apply hyp.vd_ne_one hG
    rw [← hyp.card_V_eq_vd, ← hU, hbot, Subgroup.card_bot]
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hDT : hyp.D ≤ hyp.T := (hyp.D_eq ▸ inf_le_left : hyp.D ≤ hyp.V).trans
    ((by rw [hyp.T_deriv_eq_QV]; exact le_sup_right : hyp.V ≤ derivedInG hyp.T).trans
      (Subgroup.map_subtype_le _))
  have hQn : (hyp.Q.subgroupOf hyp.T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).mpr (by
      rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T)
  have hDn : (hyp.D.subgroupOf hyp.T).Normal := by
    have hnorm := OddOrder.Peterfalvi.S12.typePData_C_normalized_by_M tpd hUne
    rw [hU, show tpd.H = hyp.Q from by rw [tpd.H_eq, hyp.Q_eq_TF], ← hyp.D_eq] at hnorm
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hDT).mpr hnorm
  have hKeq : hyp.K.subgroupOf hyp.T = hyp.Q.subgroupOf hyp.T ⊔ hyp.D.subgroupOf hyp.T := by
    rw [← Subgroup.subgroupOf_sup hQT hDT]; rfl
  rw [hKeq]
  infer_instance

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseACoherence.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

set_option linter.unusedFintypeInType false in
/-- **Constituent kernel step for (1.5.a)** (Coq `S1cases` inner kernel argument), stated
generically.  For subgroups `P0, K'` of a finite group `Γ`, an irreducible `s ∈ Irr(Γ)`, and an
irreducible `θ'` of `K'` with `P0.subgroupOf K' ⊄ ker θ'`: if `θ'` is a constituent of
`Res_{K'} s` (`⟨θ', Res_{K'} s⟩ ≠ 0`), then `P0 ⊄ ker s`.

**Contrapositive.**  `P0 ⊆ ker s` makes `Res_{K'} s` trivial on `P0.subgroupOf K'`
(`characterKernel_restrict_subgroupOf`); `θ'`, a constituent of the genuine character `Res_{K'} s`
(`isCharacter_restrict`), inherits the containment
(`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), so `P0.subgroupOf K' ⊆ ker θ'`,
contradicting the hypothesis.  This is the `S`-instance analogue of the leaf
`PrimeTIResidue.constituent_P_not_subset_ker`, grounded on the honest `S'`-family — no
`PrimeTIResidueData` and no prime-TI dichotomy is used. -/
theorem constituent_P_not_subset_characterKernel {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] (P0 K' : Subgroup Γ) [Fintype ↥K']
    [Invertible (Nat.card ↥K' : ℂ)]
    (θ' : ClassFunction ↥K' ℂ)
    (hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθ'P : ¬ ((P0.subgroupOf K' : Set ↥K') ⊆ OddOrder.Peterfalvi.S03.characterKernel θ'))
    (s : OddOrder.RepresentationTheory.IrreducibleCharacter Γ)
    (hs : ClassFunction.inner θ' (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) ≠ 0) :
    ¬ ((P0 : Set Γ) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction Γ ℂ)) := by
  intro hker
  have hResChar : IsCharacter (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter K'
  have hinner' : ClassFunction.inner
      (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) θ' ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    exact star_ne_zero.mpr hs
  have hResker : ((P0.subgroupOf K') : Set ↥K') ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf K' hker
  exact hθ'P fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hθ'irr hinner' (hResker hx)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_Tau1T.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(1.5.a)-at-`T`, `ℤ[𝒯 ∩ Irr T]` membership for irreducible `K`-inductions** (mirror of
`induce_H_mem_zSpan_sSet_irr`; Coq `S1cases` irreducible branch at `T`): if additionally
`Ind_K^T θ` is itself irreducible, every nonzero-coefficient `T'`-constituent induction is an
*irreducible* member of `𝒯`.  Otherwise some constituent is a ν-row
(`sSet_reducible_eq_nuRowSum`) — but `⟨Ind_K θ, ν_i⟩ = 0` (distinct-source `K`-inductions of
the irreducible `Ind_K θ` vs the reducible `ν_i = Ind_K θ_i`, `nu_i_isIndQD`), while the
constituent expansion makes that inner product a sum of non-negative integers with the
offending term `k·p > 0`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθQ : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) :
    ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ ∈
      OddOrder.Peterfalvi.S07.zSpan
        {ψ : ClassFunction ↥hyp.T ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) ∧
          OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ} := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.T := Fintype.ofFinite _
  let : Fintype ↥((derivedInG hyp.T).subgroupOf hyp.T) := Fintype.ofFinite _
  let : Fintype ↥(hyp.K.subgroupOf hyp.T) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥((derivedInG hyp.T).subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hyp.K.subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set data := hyp.toTypesIIIIIIVSetupT hG hvd with hdata
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  set HU : Subgroup ↥hyp.T := OddOrder.Peterfalvi.S11.huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.T).subgroupOf hyp.T :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data
  let : Fintype ↥HU := Fintype.ofFinite _
  let : Invertible (Nat.card ↥HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hKderiv : hyp.K ≤ derivedInG hyp.T := by
    change hyp.Q ⊔ hyp.D ≤ derivedInG hyp.T
    rw [hyp.T_deriv_eq_QV]
    exact sup_le le_sup_left (le_trans (hyp.D_eq ▸ inf_le_left) le_sup_right)
  have hKle : hyp.K.subgroupOf hyp.T ≤ HU := by
    rw [hHUeq]; exact Subgroup.subgroupOf_mono hyp.T hKderiv
  let : Fintype ↥((hyp.K.subgroupOf hyp.T).subgroupOf HU) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥((hyp.K.subgroupOf hyp.T).subgroupOf HU) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hKle).surjective hθ
  have hθ'Q : ¬ ((((hyp.Q.subgroupOf hyp.T).subgroupOf HU).subgroupOf
        ((hyp.K.subgroupOf hyp.T).subgroupOf HU) :
      Set ↥((hyp.K.subgroupOf hyp.T).subgroupOf HU)) ⊆
    OddOrder.Peterfalvi.S03.characterKernel
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)) := by
    rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
    have himg : (((hyp.Q.subgroupOf hyp.T).subgroupOf HU).subgroupOf
          ((hyp.K.subgroupOf hyp.T).subgroupOf HU)).map
          (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        = (hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) := by
      ext y
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf]
      rfl
    rw [himg]; exact hθQ
  -- Two-stage constituent expansion with `ℕ`-coefficients `k s`.
  have hzeta : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
      = ∑ s : IrreducibleCharacter ↥HU,
          ClassFunction.inner
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
            (ClassFunction.restrict ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
              (s : ClassFunction ↥HU ℂ))
            • ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) := by
    rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hKle θ,
      OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ),
      ClassFunction.induce_sum]
    exact Finset.sum_congr rfl fun s _ => ClassFunction.induce_smul _ _ _
  have hcoefNat : ∀ s : IrreducibleCharacter ↥HU, ∃ n : ℕ,
      ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) = (n : ℂ) := by
    intro s
    have hResChar : IsCharacter (ClassFunction.restrict
        ((hyp.K.subgroupOf hyp.T).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
      OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
    obtain ⟨n, hn⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
    exact ⟨n, by rw [OddOrder.RepresentationTheory.inner_conj_symm, hn, star_natCast]⟩
  choose k hk using hcoefNat
  -- Nonzero-coefficient constituents give family members (`Q ⊄ Ker s`, membership by witness).
  have hmem : ∀ s : IrreducibleCharacter ↥HU, k s ≠ 0 →
      ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈ sSet data := by
    intro s hks
    rw [OddOrder.Peterfalvi.S11.mem_sSet]
    refine ⟨s, ?_, rfl⟩
    change ¬ ((OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
    have hHInHu : (OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU)
        = ((hyp.Q.subgroupOf hyp.T).subgroupOf HU : Set ↥HU) := by
      congr 1
      change (data.H.subgroupOf hyp.T).subgroupOf HU = (hyp.Q.subgroupOf hyp.T).subgroupOf HU
      rw [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd]
    rw [hHInHu]
    have hs : ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
      rw [hk s]; exact_mod_cast hks
    exact constituent_P_not_subset_characterKernel ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
      ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) hθ'irr hθ'Q s hs
  -- **The upgrade**: every nonzero-coefficient constituent induction is irreducible.
  have hirrall : ∀ s : IrreducibleCharacter ↥HU, k s ≠ 0 →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ)) := by
    intro s₀ hk₀
    by_contra hred
    -- a reducible member is a nonzero ν-row ((13.3.a)-at-`T` reverse dichotomy)
    obtain ⟨i, hi, hνeq₀⟩ := hyp.sSet_reducible_eq_nuRowSum hG pins hvd (hmem s₀ hk₀) hred
    obtain ⟨θi, hθiirr, -, hνeq⟩ := hyp.nu_i_isIndQD hG pins i hi
    -- `Ind θ ≠ ν_i` (irreducible vs. reducible), so the distinct `K`-inductions are orthogonal
    have hne' : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
        ≠ ClassFunction.induce (hyp.K.subgroupOf hyp.T) θi := by
      intro h
      exact hyp.nuRow_not_irreducible pins i (by rw [hνeq, ← h]; exact hind)
    have hKnorm : (hyp.K.subgroupOf hyp.T).Normal := hyp.K_subgroupOf_T_normal hG
    have hzmu : ClassFunction.inner (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
        (∑ j : Fin hyp.p, hyp.nu i j) = 0 := by
      rw [hνeq]
      refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj
        (⟨θ, hθ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _)
        (⟨θi, hθiirr⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _) ?_
      intro g hg
      apply hne'
      have h1 : ClassFunction.induce (hyp.K.subgroupOf hyp.T)
          ((OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy g
              (⟨θ, hθ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _) :
            OddOrder.RepresentationTheory.IrreducibleCharacter _) :
              ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
          = ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ := by
        rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy]
        exact OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq
          (G := ↥hyp.T) (H := hyp.K.subgroupOf hyp.T) g _
      rw [← h1, hg]
    -- expand `⟨Ind θ, ν_i⟩` through the constituent sum: non-negative integer terms
    have hexp : ClassFunction.inner (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
        (∑ j : Fin hyp.p, hyp.nu i j)
        = ∑ s : IrreducibleCharacter ↥HU, (k s : ℂ) *
            ClassFunction.inner (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
              (∑ j : Fin hyp.p, hyp.nu i j) := by
      rw [hzeta, OddOrder.RepresentationTheory.inner_sum_left]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hk s, OddOrder.RepresentationTheory.ClassFunction.inner_smul_left]
    have hνmem : (∑ j : Fin hyp.p, hyp.nu i j) ∈ sSet data :=
      OddOrder.Peterfalvi.S11.sOf_subset_sSet data chief.H0
        (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief i hi)
    have hterm : ∀ s : IrreducibleCharacter ↥HU, ∃ n : ℕ,
        (k s : ℂ) * ClassFunction.inner (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
          (∑ j : Fin hyp.p, hyp.nu i j) = (n : ℂ) := by
      intro s
      rcases Nat.eq_zero_or_pos (k s) with h0 | hpos
      · exact ⟨0, by rw [h0]; simp⟩
      · by_cases heq : ClassFunction.induce HU (s : ClassFunction ↥HU ℂ)
            = ∑ j : Fin hyp.p, hyp.nu i j
        · refine ⟨k s * hyp.p, ?_⟩
          rw [heq, hyp.nuRow_inner pins i i, if_pos rfl]
          push_cast
          ring
        · refine ⟨0, ?_⟩
          rw [sSet_pairwiseOrthogonal data (hmem s hpos.ne') hνmem heq, mul_zero, Nat.cast_zero]
    choose n hn using hterm
    -- the total is `0`, so every `ℕ`-term vanishes — but the `s₀`-term is `k s₀ · p > 0`
    have hsumC : ∑ s : IrreducibleCharacter ↥HU, ((n s : ℕ) : ℂ) = 0 := by
      rw [Finset.sum_congr rfl fun s _ => (hn s).symm, ← hexp, hzmu]
    have hsumN : ∑ s : IrreducibleCharacter ↥HU, n s = 0 := by
      rw [← Nat.cast_sum] at hsumC
      exact_mod_cast hsumC
    have hn0 : n s₀ = 0 :=
      (Finset.sum_eq_zero_iff.mp hsumN) s₀ (Finset.mem_univ s₀)
    have hval : (k s₀ : ℂ) * ClassFunction.inner
        (ClassFunction.induce HU (s₀ : ClassFunction ↥HU ℂ))
        (∑ j : Fin hyp.p, hyp.nu i j) = (k s₀ : ℂ) * (hyp.p : ℂ) := by
      rw [hνeq₀, hyp.nuRow_inner pins i i, if_pos rfl]
    have : ((n s₀ : ℕ) : ℂ) ≠ 0 := by
      rw [← hn s₀, hval]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hk₀)
        (Nat.cast_ne_zero.mpr hyp.p_prime.pos.ne')
    exact this (by rw [hn0, Nat.cast_zero])
  -- assemble: the expansion lands in `ℤ[𝒯 ∩ Irr T]`
  rw [hzeta]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [hk s]
  rcases Nat.eq_zero_or_pos (k s) with h0 | hpos
  · rw [h0]; simp
  · rw [Nat.cast_smul_eq_nsmul ℂ (k s)]
    have hmemIrr : ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈
        {ψ : ClassFunction ↥hyp.T ℂ | ψ ∈ sSet data ∧
          OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ} :=
      ⟨hmem s hpos.ne', hirrall s hpos.ne'⟩
    exact nsmul_mem (Submodule.subset_span hmemIrr) (k s)

end OddOrder.Peterfalvi.S15
