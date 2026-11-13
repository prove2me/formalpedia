-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.induce_H_mem_zSpan_sSet_irr
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:54:39.12814+00:00
-- url     : https://prove2.me/submissions/5f7b935a-8a5f-4f29-a1ce-2b53ce57ab87

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/ChiefFactorBasic.lean
--   OddOrder/Peterfalvi/S15_CaseACoherence.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide

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

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

set_option maxHeartbeats 800000 in
-- raised heartbeat budget for the heavy elaboration below
open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The irreducible branch of Coq's `S1cases`** (`PFsection13.v:401-428`, issue 2035): an
*irreducible* induced character `Ind_{PC}^S θ` (`θ ∈ Irr H`, `P ⊄ Ker θ`) lies in
`ℤ[𝒮 ∩ Irr S]` — the integral span of the *irreducible* members of the honest §9 family
(Coq's `'Z[calSirr]`).

**Proof.**  As in `induce_H_mem_zSpan_S`, the two-stage expansion writes
`Ind_{PC}^S θ = ∑_s ⟨θ', Res s⟩ • Ind_{S'}^S s` over `S'`-constituents with `ℕ`-coefficients,
each nonzero-coefficient constituent having `P ⊄ Ker s` (hence `Ind_{S'}^S s ∈ 𝒮`).  The upgrade:
every such member is *irreducible*.  Otherwise it is a `μ`-column `μ_j = ∑_i μ_{ij}`
(`sSet_reducible_eq_muColumnSum`), and the expansion pairs to
`⟨Ind θ, μ_j⟩ = ∑_t k_t·⟨Ind_{S'} t, μ_j⟩`, a sum of non-negative integers with the offending
term `k_{s₀}·q > 0` (`𝒮`-members are pairwise orthogonal, `‖μ_j‖² = q`); but `⟨Ind θ, μ_j⟩ = 0`
since `μ_j = Ind_{PC}^S θ_j` ((13.3.a)) is a *distinct* `H`-induction (equality would make the
irreducible `Ind θ` equal the reducible `μ_j`), and distinct-source `H`-inductions are
orthogonal (`inner_induce_eq_zero_of_not_conj`). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) :
    ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∈
      OddOrder.Peterfalvi.S07.zSpan
        {ψ : ClassFunction ↥hyp.S ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) ∧
          OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ} := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Fintype ↥((derivedInG hyp.S).subgroupOf hyp.S) := Fintype.ofFinite _
  let : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥((derivedInG hyp.S).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  set HU : Subgroup ↥hyp.S := OddOrder.Peterfalvi.S11.huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.S).subgroupOf hyp.S :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data
  let : Fintype ↥HU := Fintype.ofFinite _
  let : Invertible (Nat.card ↥HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hHderiv : hyp.H ≤ derivedInG hyp.S := by
    change hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hKle : hyp.H.subgroupOf hyp.S ≤ HU := by
    rw [hHUeq]; exact Subgroup.subgroupOf_mono hyp.S hHderiv
  let : Fintype ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- The transport `θ' = θ ∘ e` of `θ` onto `PC' = (PC).subgroupOf HU ≤ HU`.
  have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hKle).surjective hθ
  have hθ'P : ¬ ((((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
        ((hyp.H.subgroupOf hyp.S).subgroupOf HU) :
      Set ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU)) ⊆
    OddOrder.Peterfalvi.S03.characterKernel
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)) := by
    rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
    have himg : (((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
          ((hyp.H.subgroupOf hyp.S).subgroupOf HU)).map
          (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        = (hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) := by
      ext y
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf]
      rfl
    rw [himg]; exact hθP
  -- Two-stage constituent expansion with `ℕ`-coefficients `k s`.
  have hzeta : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      = ∑ s : IrreducibleCharacter ↥HU,
          ClassFunction.inner
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
            (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
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
        (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) = (n : ℂ) := by
    intro s
    have hResChar : IsCharacter (ClassFunction.restrict
        ((hyp.H.subgroupOf hyp.S).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
      OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
    obtain ⟨n, hn⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
    exact ⟨n, by rw [OddOrder.RepresentationTheory.inner_conj_symm, hn, star_natCast]⟩
  choose k hk using hcoefNat
  -- Nonzero-coefficient constituents give family members (`P ⊄ Ker s`, membership by witness).
  have hmem : ∀ s : IrreducibleCharacter ↥HU, k s ≠ 0 →
      ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈ sSet data := by
    intro s hks
    rw [OddOrder.Peterfalvi.S11.mem_sSet]
    refine ⟨s, ?_, rfl⟩
    change ¬ ((OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
    have hHInHu : (OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU)
        = ((hyp.P.subgroupOf hyp.S).subgroupOf HU : Set ↥HU) := by
      congr 1
      change (data.H.subgroupOf hyp.S).subgroupOf HU = (hyp.P.subgroupOf hyp.S).subgroupOf HU
      have hPeq : data.H = hyp.P := by
        change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
      rw [hPeq]
    rw [hHInHu]
    have hs : ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
      rw [hk s]; exact_mod_cast hks
    exact constituent_P_not_subset_characterKernel ((hyp.P.subgroupOf hyp.S).subgroupOf HU)
      ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) hθ'irr hθ'P s hs
  -- **The upgrade**: every nonzero-coefficient constituent induction is irreducible.
  have hirrall : ∀ s : IrreducibleCharacter ↥HU, k s ≠ 0 →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ)) := by
    intro s₀ hk₀
    by_contra hred
    -- a reducible member is a nonzero `μ`-column ((13.3.a) reverse dichotomy)
    obtain ⟨j, hj, hμeq₀⟩ := hyp.sSet_reducible_eq_muColumnSum hG (hmem s₀ hk₀) hred
    obtain ⟨θj, hθjirr, -, hμeq⟩ := hyp.mu_j_isIndPC hG j hj
    -- `Ind θ ≠ μ_j` (irreducible vs. reducible), so the distinct `H`-inductions are orthogonal
    have hne' : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
        ≠ ClassFunction.induce (hyp.H.subgroupOf hyp.S) θj := by
      intro h
      exact hyp.mu_colSum_not_irreducible j (by rw [hμeq, ← h]; exact hind)
    have hKnorm : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
    have hzmu : ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
        (∑ i : Fin hyp.q, hyp.mu i j) = 0 := by
      rw [hμeq]
      refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj
        (⟨θ, hθ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _)
        (⟨θj, hθjirr⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _) ?_
      intro g hg
      apply hne'
      have h1 : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          ((OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy g
              (⟨θ, hθ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _) :
            OddOrder.RepresentationTheory.IrreducibleCharacter _) :
              ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
          = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ := by
        rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy]
        exact OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq
          (G := ↥hyp.S) (H := hyp.H.subgroupOf hyp.S) g _
      rw [← h1, hg]
    -- expand `⟨Ind θ, μ_j⟩` through the constituent sum: non-negative integer terms
    have hexp : ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
        (∑ i : Fin hyp.q, hyp.mu i j)
        = ∑ s : IrreducibleCharacter ↥HU, (k s : ℂ) *
            ClassFunction.inner (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
              (∑ i : Fin hyp.q, hyp.mu i j) := by
      rw [hzeta, OddOrder.RepresentationTheory.inner_sum_left]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hk s, OddOrder.RepresentationTheory.ClassFunction.inner_smul_left]
    have hμmem : (∑ i : Fin hyp.q, hyp.mu i j) ∈ sSet data :=
      OddOrder.Peterfalvi.S11.sOf_subset_sSet data chief.H0
        (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)
    have hterm : ∀ s : IrreducibleCharacter ↥HU, ∃ n : ℕ,
        (k s : ℂ) * ClassFunction.inner (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
          (∑ i : Fin hyp.q, hyp.mu i j) = (n : ℂ) := by
      intro s
      rcases Nat.eq_zero_or_pos (k s) with h0 | hpos
      · exact ⟨0, by rw [h0]; simp⟩
      · by_cases heq : ClassFunction.induce HU (s : ClassFunction ↥HU ℂ)
            = ∑ i : Fin hyp.q, hyp.mu i j
        · refine ⟨k s * hyp.q, ?_⟩
          rw [heq, hyp.muColumn_inner_self j]
          push_cast
          ring
        · refine ⟨0, ?_⟩
          rw [sSet_pairwiseOrthogonal data (hmem s hpos.ne') hμmem heq, mul_zero, Nat.cast_zero]
    choose n hn using hterm
    -- the total is `0`, so every `ℕ`-term vanishes — but the `s₀`-term is `k s₀ · q > 0`
    have hsumC : ∑ s : IrreducibleCharacter ↥HU, ((n s : ℕ) : ℂ) = 0 := by
      rw [Finset.sum_congr rfl fun s _ => (hn s).symm, ← hexp, hzmu]
    have hsumN : ∑ s : IrreducibleCharacter ↥HU, n s = 0 := by
      rw [← Nat.cast_sum] at hsumC
      exact_mod_cast hsumC
    have hn0 : n s₀ = 0 :=
      (Finset.sum_eq_zero_iff.mp hsumN) s₀ (Finset.mem_univ s₀)
    have hval : (k s₀ : ℂ) * ClassFunction.inner
        (ClassFunction.induce HU (s₀ : ClassFunction ↥HU ℂ))
        (∑ i : Fin hyp.q, hyp.mu i j) = (k s₀ : ℂ) * (hyp.q : ℂ) := by
      rw [hμeq₀, hyp.muColumn_inner_self j]
    have : ((n s₀ : ℕ) : ℂ) ≠ 0 := by
      rw [← hn s₀, hval]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hk₀)
        (Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne')
    exact this (by rw [hn0, Nat.cast_zero])
  -- assemble: the expansion lands in `ℤ[𝒮 ∩ Irr S]`
  rw [hzeta]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [hk s]
  rcases Nat.eq_zero_or_pos (k s) with h0 | hpos
  · rw [h0]; simp
  · rw [Nat.cast_smul_eq_nsmul ℂ (k s)]
    have hmemIrr : ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈
        {ψ : ClassFunction ↥hyp.S ℂ | ψ ∈ sSet data ∧
          OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ} :=
      ⟨hmem s hpos.ne', hirrall s hpos.ne'⟩
    exact nsmul_mem (Submodule.subset_span hmemIrr) (k s)

end OddOrder.Peterfalvi.S15
