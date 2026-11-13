-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.CharacterDegreeCore.lambda_tau1_sharp_norm_lower_core
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:01:38.018496+00:00
-- url     : https://prove2.me/submissions/f4a2e8c0-ad4e-47aa-8f86-ae1d3d292c5a

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_Building78C.lean
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Canonicalization.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/HSharpChosenBase.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/LambdaCorrection.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_exists_lambda_alphaFun_one_qb_base
import Theorems.Thm_OddOrder_Peterfalvi_S15_H_sharp_hypothesis76_base_alphaFun_inflation
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_tau1_cCoeff_base
import Theorems.Thm_OddOrder_Peterfalvi_S15_hypothesis76_zeta_inner_alphaFun_eq_zero
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient

-- ===== OddOrder/Peterfalvi/S09_Building78C.lean =====
namespace OddOrder.Peterfalvi.S09.Cert

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L]

/-- **The chosen-base normalization pins `ζ₀ = Ind_H^L φ₀`.** -/
theorem hypothesis76OfDadeBase_zeta_zero
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    (φ₀ :
      haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
      IrreducibleCharacter ↥(H.subgroupOf L)) :
    haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
    haveI : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    (hypothesis76OfDadeBase H71 hτ H hHL hHnorm hAH φ₀).zeta 0
      = ClassFunction.induce (H.subgroupOf L) (φ₀ : ClassFunction ↥(H.subgroupOf L) ℂ) := by
  have hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  let : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  unfold hypothesis76OfDadeBase hypothesis76OfFamily
  dsimp only
  rw [Equiv.swap_apply_left]
  have h := Classical.choose_spec ((distinctInducedFamily (H.subgroupOf L)).cover φ₀)
  dsimp only at h
  exact h

end OddOrder.Peterfalvi.S09.Cert

-- ===== OddOrder/Peterfalvi/S13_TypeDetermination.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

/-- **Peterfalvi (11.9.b), character core** (Peterfalvi §11
coherence / Dade norm).  For a Type III/IV maximal subgroup `S` (the Hypothesis (11.2) case), with
κ-Hall factor `K` and dual factor `K* = M_σ(S) ⊓ C_G(K)`, the coherence / norm-inequality bound on
the character set `S(HC)` forces `q > p`, i.e. the dual factor is the smaller: `|K*| < |K|`
(`q = |W₁| = |K|`, `p = |W₂| = |K*|`).

The proof is now **fully assembled** from three pieces: (i) the carrier translation `|K| = w₁` (both
`K` and `W₁` complement `M'`, so both equal the derived index — `card_kappaHall_eq_derived_index`,
`TypePData.card_W1_eq_derived_index`); (ii) the carrier translation `|K*| = w₂`
(`card_Msigma_inf_centralizer_eq_card_W2`, axiom-clean BG §14 group theory); and (iii) the §11
character reduction `w₂ < w₁` (`S13.w2_lt_w1_of_hypothesis_H0C_unconditional` — the honest
narrow-`𝒮(H₀C)` route on the unconditional (11.3), issues 1019/1020; the deprecated wide
`S12.w2_lt_w1_of_hypothesis` and its false uniform-degree lemma have been retired).  All of
(i)/(ii) and the reduction spine of (iii) are proven; the residual is the genuine Peterfalvi
(11.8) non-orthogonality (`S13.exists_zeta_residual_not_orthogonal_H0C_of_refuter`), which
rests on the §14 Sibley glue `(6.7)`/`(5.8)` and the `(9.11)` caseA refuter (the `(10.8)`
residual is discharged by `S_not_coherent_unconditional`).  All of these are now proved. -/
theorem card_kappaHall_lt_of_isTypeIIIorIV {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hIIIorIV : IsTypeIII S ∨ IsTypeIV S) :
    Nat.card ↥Kstar < Nat.card ↥K := by
  -- `K` is cyclic, as a subgroup of the cyclic `Z = K ⊔ K*` (BG 14.7(d), via `typeP_duality`).
  obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
    BG.Ch4.S14.typeP_duality hG hS hSP hKS hK hKstar
  have : IsCyclic ↥(K ⊔ Kstar) := hcyc
  have : IsCyclic ↥K :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Kstar))
      (Subgroup.inclusion_injective _)
  -- Build the §10 hypothesis on `S` (type III/IV ⊆ III/IV/V).
  obtain ⟨hyp⟩ := OddOrder.Peterfalvi.S12.exists_hypothesis_of_typeIIIorIVorV hG hS
    (hIIIorIV.imp id Or.inl)
  -- `|K| = w₁`: both `K` and `W₁` complement `M'`, so both equal the derived index.
  have hKw1 : Nat.card ↥K = hyp.w1 := by
    rw [BG.Ch4.S16.card_kappaHall_eq_derived_index hG hS hSP hKS hK]
    exact hyp.typeP.card_W1_eq_derived_index.symm
  -- `|K*| = w₂`: the carrier bridge (lane-b W3, BG §14 group theory, now in `S10`).
  have hKstarw2 : Nat.card ↥Kstar = hyp.w2 := by
    rw [hKstar]
    exact OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2 hG hS hSP hKS hK hyp.typeP
  -- The two (11.5)/(11.7) structural facts, discharged via §13 (`secondDerived_eq_HC`,
  -- `H_elementaryAbelian`): `M'' = H ⊔ C_U(H)` and `|H| = |W₂|^{|W₁|}`.
  have hM2 : secondDerivedInAmbient S
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)) :=
    OddOrder.Peterfalvi.S13.secondDerived_eq_fitting_of_base hG hyp hIIIorIV
      (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
  have hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1 :=
    OddOrder.Peterfalvi.S13.card_H_eq_of_base hG hyp hIIIorIV
      (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
  -- `w₂ < w₁` (Peterfalvi (11.9.b), from the genuine (11.8) via the honest narrow `𝒮(H₀C)` route
  -- on the unconditional (11.3) — `w2_lt_w1_of_hypothesis_H0C_unconditional`, issues 1019/1020).
  rw [hKstarw2, hKw1]
  exact OddOrder.Peterfalvi.S13.w2_lt_w1_of_hypothesis_H0C_unconditional hG hyp hIIIorIV hM2
    hHcard

/-- **Peterfalvi (13.2.a), character core** (mmd §13, `references/peterfalvi/04.15_*`).

For the type-`P` member `S` of a dual maximal pair (BG Theorem 14.7), with κ-Hall factor `K` and
dual factor `K* = M_σ(S) ⊓ C_G(K)`, the type-`P₁` alternative (`S` of Type III/IV/V) carries the
*larger* κ-Hall factor: `|K*| < |K|`.  In Peterfalvi's notation `q = |W₁| = |K|`, `p = |W₂| = |K*|`,
this is "`S` of Type III ⟹ `q > p`".

**Type-V exclusion via the unconditional Theorem (10.10)** (issue 1020 Phase 3 relayering): by
the type dictionary `proposition_type_classification`, a type-`P₁` `S` is Type III/IV (if
`M_F ≠ M_σ`) or Type V (if `M_F = M_σ`); the latter is impossible by
`no_typeV_maximal_unconditional` (`S12_Noncoherence` — the honest (10.8) → (10.10) chain,
including the (6.5) gate lemmas of issue 2022), so `S` is Type III/IV and the
genuinely §11 character core `card_kappaHall_lt_of_isTypeIIIorIV` ((11.9.b)) applies.  Consumed
by `isTypeP2_of_typeP_kappaHall_lt`. -/
theorem card_kappaHall_lt_of_isTypeP1 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hP1 : BG.Ch4.S14.IsTypeP1 S) :
    Nat.card ↥Kstar < Nat.card ↥K := by
  -- Type dictionary: `S` type-`P₁` ⟹ Type III/IV (`M_F ≠ M_σ`) or Type V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ := BG.Ch4.S16.proposition_type_classification hG hS
  -- Type V is excluded by Theorem (10.10) `no_typeV_maximal`, so `M_F ≠ M_σ` and `S` is III/IV.
  have hMF : BG.Ch4.S15.MF S ≠ BG.Ch3.S10.Msigma S := fun hMF =>
    OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG ⟨S, hS, hdV.mpr ⟨hP1, hMF⟩⟩
  -- The genuinely §11 character core (11.9.b) gives `|K*| < |K|`.
  exact card_kappaHall_lt_of_isTypeIIIorIV hG hS hSP hKS hK hKstar (hcIII_IV.mpr ⟨hP1, hMF⟩)

/-- **Peterfalvi (13.2.a)** (mmd §13, `references/peterfalvi/04.15_*`): the type-`P` member `S` of a
dual maximal pair whose κ-Hall factor `K` is the *smaller* of the two coprime factors of
`W = K × K*` is of type `P₂` (BG) / Type II (Peterfalvi).

This selects, out of the type-duality disjunction `IsTypeP2 S ∨ IsTypeP2 T` (BG Theorem 14.7,
`typeP_duality`, which carries no order information), the determinate side `IsTypeP2 S` fixed by the
ordering `|K| < |K*|`.  Skeleton proof: `S` is type-`P`, hence type `P₁` or `P₂`
(`isTypeP_iff_isTypeP1_or_isTypeP2`); the `P₁` branch is excluded by `card_kappaHall_lt_of_isTypeP1`
(the Pf §10–§11 character core), leaving `P₂`.

Consumed by `section16MaximalPair_of_isMinimalSimpleOdd` to carry `Section16MaximalPair.S_typeP2`
(relane #4, issues 4009/2019), which unblocks the §15 `basic_structure` `TypePData` carrier wiring
(`exists_typePData_W1_eq_of_isTypeP2`). -/
theorem isTypeP2_of_typeP_kappaHall_lt {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hlt : Nat.card ↥K < Nat.card ↥Kstar) :
    BG.Ch4.S14.IsTypeP2 S := by
  rcases BG.Ch4.S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hSP with hP1 | hP2
  · exact absurd (card_kappaHall_lt_of_isTypeP1 hG hS hSP hKS hK hKstar hP1) (lt_asymm hlt)
  · exact hP2

end OddOrder

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.b,c,e) — the `M_F`-structure residual** (faithful obligation, §16-gated).

The genuinely §16-structural half of (13.2): the Fitting kernel `P = S_F` is elementary abelian of
order `p^q` (13.2.b,c), the complement `U` is abelian (13.2.a), `u ≤ (p^q − 1)/(p − 1)` (13.2.e),
and `A_0(S)` is a TI-subset (13.2.e).

Unlike the *type determination* and the `U W₁` *Frobenius structure* of (13.2.a) — both now read off
sorry-free from the carrier (`isTypeII_of_isTypeP2`, `typeP_uW1_frobenius` on `Sdata`) — these are
the σ-structure facts of the type-`P₂` member `S`: `M_σ = M_F` is the elementary-abelian `p`-group
of
rank `q` on which the prime-order `κ`-Hall factor `W₁` acts (BG §10/§14 σ-theory), giving the
`u`-bound from the count of `W₁`-orbits.  No repo theorem yet states "`M_σ` elementary abelian of
order `p^q`"; declared here as the localized faithful gate (the
`card_Q_eq`/`coprime_card_U_card_P_of_disjoint` pattern) so that `basic_structure`'s assembly — its
honest type determination and Frobenius structure — are `sorry`-free. -/
structure BasicStructureGated (hyp : Hypothesis (G := G)) where
  U_commutative : IsMulCommutative ↥hyp.U
  P_elementaryAbelian : IsElementaryAbelian hyp.p ↥hyp.P
  P_order : Nat.card ↥hyp.P = hyp.p ^ hyp.q
  u_bound : hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1)
  A0S_TI : Prop
  A0S_TI_holds : A0S_TI
  tauS_eq_induction : Prop
  tauS_eq_induction_holds : tauS_eq_induction

/-- **(Rung B, reduction) `IsTISubset (A(S)) S ⟹ all `S`-instance Dade stabilizers vanish.**  A
TI-subset `A` has `C_G(x) ≤ L` for every `x ∈ A` (`IsTISubset.centralizer_le`), so no `A(S)`-point
escapes `S`; then `forall_dadeHypS_H_eq_bot_of_not_escaping` applies.  This is the direction of
Peterfalvi (2.3) that turns the `normedTI` conclusion (Rung C/D) into the trivial-stabilizer datum
the honest `dade = Ind` bridge consumes. -/
theorem Hypothesis.forall_dadeHypS_H_eq_bot_of_isTISubset [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTI : OddOrder.GroupTheory.IsTISubset (S10.typePACore hyp.S) hyp.S) :
    ∀ a : {a : G // a ∈ S10.typePACore hyp.S}, (hyp.dadeHypS hG).H a = ⊥ :=
  hyp.forall_dadeHypS_H_eq_bot_of_not_escaping hG
    (fun _a ha hesc => hesc.2 (hTI.centralizer_le ha))

/-- **(Rung B, the equivalence, Peterfalvi (2.3) for the honest `S`-instance)**: the three forms of
the (13.2.e) `normedTI` gate coincide —
`IsTISubset (A(S)) S` ⟺ every `A(S)`-point is non-escaping ⟺ every `S`-instance Dade stabilizer
`dadeHypS.H a` is trivial.

The `A(S)`-set is sharp (`S10.typePACore_subset_sharp`, `1 ∉ A(S)`), lies in `S`
(`S10.typePACore_subset`), and is `S`-conjugation invariant (`S10.typePACore_conj_mem`), so the
general `S04.isTISubset_iff_exists_hypothesis_with_trivial_H` (2.3) applies; but here we get the
*specific* `dadeHypS` stabilizers, via the (8.14) kernel formula.  This closes Rung B: reducing the
missing input of `sInstance_dade_eq_induce_of_supported_trivial_H` (with `A₁ = A(S)` full) to the
single TI fact `IsTISubset (A(S)) S` = Coq `FTtypeP_facts` (e). -/
theorem Hypothesis.isTISubset_typePACore_iff_forall_dadeHypS_H_eq_bot [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.GroupTheory.IsTISubset (S10.typePACore hyp.S) hyp.S ↔
      ∀ a : {a : G // a ∈ S10.typePACore hyp.S}, (hyp.dadeHypS hG).H a = ⊥ := by
  refine ⟨hyp.forall_dadeHypS_H_eq_bot_of_isTISubset hG, fun hH => ?_⟩
  -- The reverse direction is Peterfalvi (2.3): trivial Dade stabilizers ⟹ TI.
  exact (hyp.dadeHypS hG).isTISubset_of_forall_H_eq_bot hH

/-- **(13.2.e) `normedTI`, TI half — `A(S)` is a TI-subset with normalizer `S`** (Coq
`FTtypeP_facts` (e), the `normedTI 'A0(S) G S` conclusion; PFsection13.v:197).  Closes the
gate G2 of issue 1017 update #22: Rung B's equivalence fed by Rung C. -/
theorem Hypothesis.isTISubset_typePACore [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) :
    OddOrder.GroupTheory.IsTISubset (S10.typePACore hyp.S) hyp.S := by
  have : Fintype G := Fintype.ofFinite G
  exact (hyp.isTISubset_typePACore_iff_forall_dadeHypS_H_eq_bot hG).mpr
    (hyp.forall_dadeHypS_H_eq_bot hG hnoV)

open scoped FiniteInduce in
/-- **Peterfalvi (13.2)(e), the book statement, unconditional** — *"`A₀(S)` is a TI-subset of `G`
with normalizer `S` and the Dade isometry `τ` relative to `A₀(S)` coincides with `Ind_S^G`"*
(p. 75; Coq `FTtypeP_facts` (e), the `normedTI 'A0(S) G S` + `{in 'CF(S, 'A0(S)), tau =1 'Ind}`
pair).

Both halves already exist (`isTISubset_typePACore`, `sInstance_dade_eq_induce`); this bundles
them and **discharges the Type-V exclusion** with the axiom-clean Theorem (10.10)
`S12.no_typeV_maximal_unconditional`, so the (13.2)(e) statement is available with no hypothesis
beyond `hG` and the (13.1) carrier.

Recorded because the `BasicStructureGated`/`BasicStructureData` carriers expose (13.2)(e) only as
the `Prop`-valued data fields `A0S_TI` / `tauS_eq_induction`, which `basic_structure_gated`
instantiates with `True` — a reader of `basic_structure`'s conclusion cannot see the clause
(issue 0172 §13 audit). -/
theorem Hypothesis.A0S_normedTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.GroupTheory.IsTISubset (S10.typePACore hyp.S) hyp.S ∧
      ∀ [Fintype G], ∀ {f : ClassFunction ↥hyp.S ℂ},
        f.support ⊆
            OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S →
          OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
              ((hyp.dadeHypS hG).fullDadeIsometryData) f
            = ClassFunction.induce hyp.S f :=
  ⟨hyp.isTISubset_typePACore hG (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG),
    fun {_} {_} hf =>
      hyp.sInstance_dade_eq_induce hG
        (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG) hf⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.a), ordered refinement**: if `q < p`, then `S` is of Type II.

Use the intrinsic κ-Hall factor `Sdata.W1`.  The generic type-`P` bridge identifies the order of
`M_σ(S) ∩ C_G(Sdata.W1)` with the order of `Sdata.W2`; the carried reconciliations turn the
hypothesis `q < p` into precisely the strict κ-ordering required by
`isTypeP2_of_typeP_kappaHall_lt`. -/
theorem Hypothesis.isTypeII_of_q_lt_p [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hqp : hyp.q < hyp.p) : IsTypeII hyp.S := by
  have hSP : OddOrder.BG.Ch4.S14.IsTypeP hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
  let : IsCyclic ↥hyp.Sdata.W1 := hyp.Sdata.W1_cyclic
  have hW1hall := OddOrder.Peterfalvi.S12.typePData_W1_isHallSubgroup_kappa
    hG hyp.S_maximal hSP hyp.Sdata
  have hbridge := OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2 hG
    hyp.S_maximal hSP hyp.Sdata.W1_le hW1hall hyp.Sdata
  have hlt : Nat.card ↥hyp.Sdata.W1 <
      Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓
        Subgroup.centralizer (hyp.Sdata.W1 : Set G)) := by
    rw [hbridge, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq,
      ← hyp.q_eq_card_W1, ← hyp.p_eq_card_W2]
    exact hqp
  have hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.S :=
    OddOrder.isTypeP2_of_typeP_kappaHall_lt hG hyp.S_maximal hSP hyp.Sdata.W1_le
      hW1hall rfl hlt
  exact OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hP2

/-- **Peterfalvi (13.2.b)/(11.7) for the `S`-instance**: `P = S_F` is elementary abelian of
exponent `p`.  Assembled from the §11 chief-factor data of `S` (`exists_chiefFactorData` on
`toTypesIIIIIIVSetupS`): the chief kernel `N = ⊥` (`toTypesIIIIIIVSetupS_chief_N_eq_bot`), so
`P/⊥ ≅ P` *is* the chief factor and carries `ChiefFactorData.quotient_elementaryAbelian` at the
chief prime `chief.p = p` (forced by `|P| = p^q`).  **Ungated** — the `S`-instance `H₀ = ⊥` is
proven (`P` itself is the chief factor), unlike the generic `chief_H0_eq_bot_of_noncoherent`
(then sorried, since proved).  Discharges
`basic_structure_gated.P_elementaryAbelian`. -/
theorem Hypothesis.P_elementaryAbelian [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    IsElementaryAbelian hyp.p ↥hyp.P := by
  classical
  obtain ⟨chief, _⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
  have hHeq : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P := by
    change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hN : chief.N = ⊥ := hyp.toTypesIIIIIIVSetupS_chief_N_eq_bot hG chief
  -- `chief.p = p` from `|P| = p^q = chief.p^q · |N|` with `|N| = 1`.
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
    change Nat.card ↥hyp.Sdata.W1 = hyp.q; rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [hHeq]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hq] at hquot
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplit
  have hdvd : chief.p ∣ hyp.p ^ hyp.q := by
    refine dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') ?_
    exact hsplit ▸ Dvd.intro _ rfl
  have hpp : chief.p = hyp.p :=
    (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  -- Transport `quotient_elementaryAbelian` along `↥H ⧸ ⊥ ≃* ↥H`, then rewrite `H = P`.
  have hEA : IsElementaryAbelian hyp.p ↥(hyp.toTypesIIIIIIVSetupS hG).H := by
    have h := chief.quotient_elementaryAbelian
    rw [hpp] at h
    exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot) h
  rwa [hHeq] at hEA

/-- **Peterfalvi (13.2.b,c,e)** structural producer: the `M_F`-structure of the type-`P₂` member
`S`.  Faithful obligation on the §16 σ-structure (`BasicStructureGated` docstring).

`U_commutative` (13.2.a U-side) and `P_order` (13.2.b order part) are now **genuine**:
* `U_commutative` from the carried `S_U_commutative` (BG Lemma 15.1(b)
`typeP_hall_derived_eq_and_abelian`, `U` the `(κ∪σ)'`-Hall, supplied at construction);
* `P_order` = `|P| = p^q` from `card_P_eq` fed by the carried `Sdata_W2_eq` (the intrinsic dual
factor `Sdata.W2 = C_{S'}(W₁#)` equals the abstract `W₂ = K*`, via
`typePData_of_kappaHall_hallComplement_W2`).

The `A_0(S)`/`τ_S` clauses are the opaque scaffold Props (`True`).  The two former concrete
residuals are now **genuine** (both discharged ungated on the `S`-instance `toTypesIIIIIIVSetupS`):
* `P_elementaryAbelian` — Pf (11.7), from the §11 chief factor `P = S_F` (`H₀ = ⊥`), via
  `Hypothesis.P_elementaryAbelian`;
* `u_bound` — Pf (9.7) `u ≤ (p^q−1)/(p−1)`, via `Hypothesis.u_le_cyclotomicQuotient`
  (cites the proven unconditional `S11.u_le_cyclotomicQuotient`; issue 9000 lane-b cite). -/
noncomputable def basic_structure_gated [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : BasicStructureGated hyp where
  U_commutative := hyp.S_U_commutative
  P_elementaryAbelian := hyp.P_elementaryAbelian hG
  P_order := hyp.card_P_eq hG hyp.Sdata_W2_eq
  u_bound := hyp.u_le_cyclotomicQuotient hG
  A0S_TI := True
  A0S_TI_holds := trivial
  tauS_eq_induction := True
  tauS_eq_induction_holds := trivial

/-- **Peterfalvi (13.2.a--c,e)**: `S` is type II or III, `P` is elementary
abelian of order `p^q`, `u` is bounded, and `A_0(S)` is a TI-subset.

The **type determination** (13.2.a) is discharged without the stronger `S_typeP2` carrier:
`isTypeII_or_isTypeIII_of_isTypeNonI` gives the unconditional alternative, while
`Hypothesis.isTypeII_of_q_lt_p` applies the genuine κ-ordering theorem when `q < p`.  The
remaining `M_F`-structure data (13.2.b,c) is read off the faithful §16-gated producer
`basic_structure_gated`.

**(13.2.e)** is stated *genuinely* here — `A₀(S)` is a TI-subset with normalizer `S`
(`Hypothesis.A0S_normedTI`, whose Type-V exclusion is discharged by the unconditional Theorem
(10.10)).  The carrier fields `BasicStructureData.A0S_TI` / `tauS_eq_induction` remain `Prop`-valued
placeholders that `basic_structure_gated` fills with `True`; the conclusion no longer routes
through them (issue 0172 §13 audit).  The isometry half `τ = Ind_S^G` is the second conjunct of
`A0S_normedTI`. -/
theorem basic_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ _data : BasicStructureData hyp,
      (IsTypeII hyp.S ∨ IsTypeIII hyp.S) ∧ IsElementaryAbelian hyp.p ↥hyp.P ∧
        Nat.card ↥hyp.P = hyp.p ^ hyp.q ∧
        hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) ∧
        OddOrder.GroupTheory.IsTISubset
          (OddOrder.Peterfalvi.S10.typePACore hyp.S) hyp.S := by
  -- (13.2.a): the honest II/III alternative; its witness-independent core gives `Sdata.U ≠ ⊥`.
  have hStype : IsTypeII hyp.S ∨ IsTypeIII hyp.S :=
    OddOrder.Peterfalvi.S13.isTypeII_or_isTypeIII_of_isTypeNonI
      _hG hyp.S_maximal hyp.S_nonI
  let setup := hyp.toTypesIIIIIIVSetupS _hG
  have hSdataUne := setup.nontrivial.1
  change hyp.Sdata.U ≠ ⊥ at hSdataUne
  -- (13.2.a) `U W₁` Frobenius: sorry-free from the carrier `Sdata` (`typeP_uW1_frobenius`,
  -- reconciled `Sdata.U = U`, `Sdata.W1 = W1`).
  have hUW1frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.U ⊔ hyp.W1) (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1))
        (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    rwa [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at h
  -- (13.2.b,c,e) `M_F`-structure: the localized faithful §16 producer.
  let core := basic_structure_gated _hG hyp
  refine ⟨{ S_typeII_or_typeIII := hStype
            q_lt_p_forces_typeII := hyp.isTypeII_of_q_lt_p _hG
            U_commutative := core.U_commutative
            UW1_frobenius := hUW1frob
            P_elementaryAbelian := core.P_elementaryAbelian
            P_order := core.P_order
            u_bound := core.u_bound
            A0S_TI := core.A0S_TI
            A0S_TI_holds := core.A0S_TI_holds
            tauS_eq_induction := core.tauS_eq_induction
            tauS_eq_induction_holds := core.tauS_eq_induction_holds }, ?_⟩
  exact ⟨hStype, core.P_elementaryAbelian, core.P_order, core.u_bound,
    (hyp.A0S_normedTI _hG).1⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Self inner-sum as a real squared-norm sum** (general `ClassFunction` identity).

For any class function `α : H → ℂ`, the unscaled self inner sum `Σ_g α(g)·conj(α(g))` equals the
real sum of squared norms `Σ_g ‖α(g)‖²` cast to `ℂ`.  This is the bridge between the abstract
`ClassFunction.innerSum`/`inner` API and the concrete `Σ |α(g)|²` quantities of Peterfalvi's norm
estimates (13.6)–(13.10); combined with `Σ_{H#} = Σ_H − |α(1)|²` it converts every Dade-norm
inequality into an elementary squared-norm sum.  A general fact for any finite group `H`. -/
theorem innerSum_self_eq_sum_normSq {H : Type*} [Group H] [Fintype H]
    (α : ClassFunction H ℂ) :
    ClassFunction.innerSum α α = ((∑ g : H, ‖α g‖ ^ 2 : ℝ) : ℂ) := by
  rw [ClassFunction.innerSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← starRingEnd_apply, RCLike.mul_conj]
  norm_cast

/-- **Parseval identity for class functions** (general): `Σ_g ‖α(g)‖² = |H| · ⟨α, α⟩`.

The full squared-norm sum equals `|H|` times the normalized self inner product `⟨α,α⟩ = ‖α‖²`.
Combined with `Σ_{H#} = Σ_H − ‖α(1)‖²` this is precisely the Parseval relation `s + d² = |H|·n`
consumed by `caseB_eta_norm_core` (the (13.7) core): it lets the cascade read off `s = ∑_{H#}|α|²`
from the abstract inner product `n = ⟨α,α⟩`.  Immediate from `innerSum_self_eq_sum_normSq` and
`ClassFunction.card_mul_inner`. -/
theorem sum_normSq_eq_card_mul_inner {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (α : ClassFunction H ℂ) :
    ((∑ g : H, ‖α g‖ ^ 2 : ℝ) : ℂ) = (Nat.card H : ℂ) * ClassFunction.inner α α := by
  rw [← innerSum_self_eq_sum_normSq, ClassFunction.card_mul_inner]

/-- **Parseval expansion of a real-scalar linear combination** (the algebraic core of Peterfalvi
(13.5.b)).  For complex functions `f, g` on a finite index set and a real scalar `κ`,
`∑‖κ·f + g‖² = κ²∑‖f‖² + 2κ·Re(∑ f·ḡ) + ∑‖g‖²`.  In (13.5.b) this is applied with `κ = a/‖ζ₁‖²`,
`f = ζ₁`, `g = α` on `H#`; together with the (13.5) sum facts `∑_{H#}|ζ₁|² = |S|‖ζ₁‖² − ζ₁(1)²` and
`∑_{H#} ζ₁ᾱ = −ζ₁(1)α(1)` it yields the (13.5.b) norm decomposition consumed by
`caseB_lambda_norm_core`
(13.6) and `caseB_eta01_norm_core` (13.8). -/
theorem sum_normSq_real_smul_add {ι : Type*} (s : Finset ι) (κ : ℝ) (f g : ι → ℂ) :
    (∑ x ∈ s, ‖(κ : ℂ) * f x + g x‖ ^ 2)
      = κ ^ 2 * (∑ x ∈ s, ‖f x‖ ^ 2)
        + 2 * κ * (∑ x ∈ s, f x * (starRingEnd ℂ) (g x)).re
        + (∑ x ∈ s, ‖g x‖ ^ 2) := by
  have hpt : ∀ x ∈ s, ‖(κ : ℂ) * f x + g x‖ ^ 2
      = κ ^ 2 * ‖f x‖ ^ 2 + 2 * κ * (f x * (starRingEnd ℂ) (g x)).re + ‖g x‖ ^ 2 := by
    intro x _
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]
    rw [show ((κ : ℂ) * f x) * (starRingEnd ℂ) (g x) = (κ : ℂ) * (f x * (starRingEnd ℂ) (g x)) by
        ring,
      Complex.re_ofReal_mul]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum]

open scoped Classical in
/-- **Peterfalvi (13.5), `ζ₁`-norm sum** (the (13.5.b) `firstTerm`): for a function `ζ` on `S`
vanishing outside the subgroup `H ≤ S`, the squared-norm sum over `H# = H ∖ {1}` equals the full sum
over `S` minus the value at `1`.  In (13.5) `ζ = ζ₁` vanishes on `S − H` (induced from `H`, with `P`
off the kernels), so combined with Parseval `∑_{x∈S}‖ζ₁‖² = |S|·‖ζ₁‖²`
(`sum_normSq_eq_card_mul_inner`)
this gives `∑_{H#}|ζ₁|² = |S|‖ζ₁‖² − ζ₁(1)²`, the `firstTerm` consumed by `caseB_lambda_norm_core`
(13.6) and `caseB_eta01_norm_core` (13.8). -/
theorem sum_normSq_sharp_eq_total_sub_one {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ : S → ℂ) (hvanish : ∀ x : S, x ∉ H → ζ x = 0) :
    ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase (1 : S), ‖ζ x‖ ^ 2
      = (∑ x : S, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2 := by
  have hHfull : (∑ x : S, ‖ζ x‖ ^ 2) = ∑ x ∈ Finset.univ.filter (· ∈ H), ‖ζ x‖ ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    rw [hvanish x (by simpa using hx)]; simp
  rw [hHfull, ← Finset.sum_erase_add (Finset.univ.filter (· ∈ H)) (fun x => ‖ζ x‖ ^ 2)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, H.one_mem⟩)]
  ring

open scoped Classical in
/-- **Peterfalvi (13.5), cross-term sum** (the (13.5.b) `−2a ζ₁(1)α(1)/‖ζ₁‖²` term): when the inner
sum `∑_{x∈H} ζ₁(x)·conj(α(x))` over the subgroup `H` vanishes — which holds in (13.5) because
`Res_H ζ₁` is a sum of characters with `P` *off* their kernels while every component of `α` has `P`
*in* its kernel (orthogonal constituents) — the sum over `H# = H ∖ {1}` collapses to the single
identity term: `∑_{H#} ζ₁·ᾱ = −ζ₁(1)·conj(α(1))`.  Supplies the cross term of the (13.5.b)
decomposition `sum_normSq_real_smul_add` (with `f = ζ₁`, `g = α`). -/
theorem sum_mul_conj_sharp_eq_neg_of_inner_zero {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ α : S → ℂ)
    (hinner : ∑ x ∈ Finset.univ.filter (· ∈ H), ζ x * (starRingEnd ℂ) (α x) = 0) :
    ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ζ x * (starRingEnd ℂ) (α x)
      = -(ζ 1 * (starRingEnd ℂ) (α 1)) := by
  rw [← Finset.sum_erase_add (Finset.univ.filter (· ∈ H))
    (fun x => ζ x * (starRingEnd ℂ) (α x))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, H.one_mem⟩)] at hinner
  exact eq_neg_of_add_eq_zero_left hinner

open scoped Classical in
/-- **Peterfalvi (13.5.b), norm-sum decomposition**: assembling the (13.5.a) point formula
`χ = κ·ζ₁ + α` (on `H#`, here the hypothesis `hχ`) with Parseval (`sum_normSq_real_smul_add`),
the `ζ₁`-vanishing fact (`sum_normSq_sharp_eq_total_sub_one`, needs `hvanish`) and the cross-term
fact (`sum_mul_conj_sharp_eq_neg_of_inner_zero`, needs `hinner` = `(Res_H ζ₁, α) = 0`) gives

  `∑_{H#}|χ|² = κ²(∑_S|ζ₁|² − ζ₁(1)²) − 2κ·Re(ζ₁(1)·conj α(1)) + ∑_{H#}|α|²`.

Specialised with `κ = a/‖ζ₁‖²` and the norm identity `∑_S|ζ₁|² = |S|‖ζ₁‖²`, this is the textbook
(13.5.b) `(a²/‖ζ₁‖²)(|S| − ζ₁(1)²/‖ζ₁‖²) − 2a·ζ₁(1)α(1)/‖ζ₁‖² + ∑_{H#}|α|²`, the decomposition
consumed by `caseB_lambda_norm_core` (13.6) / `caseB_eta_norm_core` (13.7) /
`caseB_eta01_norm_core` (13.8).  Generic in `(ζ₁, α, χ, κ)`; the three character-theoretic
hypotheses (`hvanish`, `hinner`, `hχ`) are discharged per-case from the (13.5.a) data. -/
theorem sum_normSq_sharp_chi_decomp {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ α χ : S → ℂ) (κ : ℝ)
    (hvanish : ∀ x : S, x ∉ H → ζ x = 0)
    (hinner : ∑ x ∈ Finset.univ.filter (· ∈ H), ζ x * (starRingEnd ℂ) (α x) = 0)
    (hχ : ∀ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, χ x = (κ : ℂ) * ζ x + α x) :
    ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖χ x‖ ^ 2
      = κ ^ 2 * ((∑ x : S, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2)
        - 2 * κ * (ζ 1 * (starRingEnd ℂ) (α 1)).re
        + ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖α x‖ ^ 2 := by
  have hstep : ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖χ x‖ ^ 2
      = ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖(κ : ℂ) * ζ x + α x‖ ^ 2 :=
    Finset.sum_congr rfl (fun x hx => by rw [hχ x hx])
  rw [hstep, sum_normSq_real_smul_add, sum_normSq_sharp_eq_total_sub_one H ζ hvanish,
    sum_mul_conj_sharp_eq_neg_of_inner_zero H ζ α hinner, Complex.neg_re]
  ring

/-- **Key nonnegativity of Peterfalvi (13.6)**: the quadratic correction term is `≥ 0`.

In (13.6) the inflation degree satisfies `α(1) = q·b` for an integer `b`, and the bound reduces to
`(|P|−1)·α(1)² − 2·λ(1)·α(1) = q²·((|P|−1)·b² − 2u·b) ≥ 0`, using `u ≤ (|P|−1)/2` from (13.2.c).
This is exactly that nonnegativity `0 ≤ (|P|−1)·b² − 2u·b` (here `Pm1 = |P| − 1`), pure
ℤ-arithmetic:
`(|P|−1)b² − 2ub = (|P|−1−2u)·b² + 2u·b(b−1)`, both summands `≥ 0` (the first by `2u ≤ |P|−1`, the
second since consecutive integers `b(b−1) ≥ 0`).  Carrier-free core of the (13.6) estimate. -/
theorem caseB_quadratic_nonneg {Pm1 u : ℕ} (hu : 2 * u ≤ Pm1) (b : ℤ) :
    0 ≤ (Pm1 : ℤ) * b ^ 2 - 2 * (u : ℤ) * b := by
  have h2u : (2 * u : ℤ) ≤ (Pm1 : ℤ) := by exact_mod_cast hu
  have hb : 0 ≤ b * (b - 1) := by
    by_cases h : 1 ≤ b
    · exact mul_nonneg (by linarith) (by linarith)
    · push Not at h
      calc 0 ≤ (-b) * (-(b - 1)) := mul_nonneg (by omega) (by omega)
        _ = b * (b - 1) := by ring
  nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (Pm1 : ℤ) - 2 * u) (sq_nonneg b),
    mul_nonneg (by positivity : (0 : ℤ) ≤ 2 * (u : ℤ)) hb]

/-- **Arithmetic assembly of Peterfalvi (13.6)**: the norm lower bound
`∑_{x∈H#}|λ^{τ₁}(x)|² ≥ |S| − λ(1)²`.

For the irreducible `λ ∈ S` of degree `λ(1) = u q` induced from a linear character of `H = PC`
(`‖λ‖² = 1`, `a = 1`), the (13.5) decomposition gives `s = (|S| − λ(1)²) − 2λ(1)α(1) + sₐ` where
`s = ∑_{H#}|λ^{τ₁}|²`, `sₐ = ∑_{H#}|α|²`. By (13.5.a)+(1.10) the correction `α(1) = q b` is
divisible
by `q`, by (13.5.c) `(|P|−1)α(1)² ≤ sₐ`, and by (13.2.c) `2u ≤ |P|−1`.  The cross terms are then
nonnegative — `−2λ(1)α(1) + (|P|−1)α(1)² = q²((|P|−1)b² − 2ub) ≥ 0` (`caseB_quadratic_nonneg`) —
whence
`|S| − λ(1)² ≤ s`.  Carrier-free arithmetic core (`Scard, Pm1, u, q` abstract naturals; the
character-theoretic decomposition is supplied by the cascade once the (13.5) engine lands). -/
theorem caseB_lambda_norm_core {Scard Pm1 u q : ℕ} {s sₐ lam1 : ℝ} {b : ℤ}
    (hlam1 : lam1 = (u : ℝ) * q)
    (hdecomp : s = ((Scard : ℝ) - lam1 ^ 2) - 2 * lam1 * ((q : ℝ) * b) + sₐ)
    (hinfl : (Pm1 : ℝ) * ((q : ℝ) * b) ^ 2 ≤ sₐ)
    (hu : 2 * u ≤ Pm1) :
    (Scard : ℝ) - lam1 ^ 2 ≤ s := by
  have hquad : (0 : ℤ) ≤ (Pm1 : ℤ) * b ^ 2 - 2 * (u : ℤ) * b := caseB_quadratic_nonneg hu b
  have hquadR : (0 : ℝ) ≤ (Pm1 : ℝ) * (b : ℝ) ^ 2 - 2 * (u : ℝ) * (b : ℝ) := by exact_mod_cast hquad
  have hcross : 0 ≤ -2 * lam1 * ((q : ℝ) * b) + sₐ := by
    have hfac : -2 * lam1 * ((q : ℝ) * b) + (Pm1 : ℝ) * ((q : ℝ) * b) ^ 2
        = (q : ℝ) ^ 2 * ((Pm1 : ℝ) * (b : ℝ) ^ 2 - 2 * (u : ℝ) * (b : ℝ)) := by
      rw [hlam1]; ring
    nlinarith [hinfl, hfac, mul_nonneg (sq_nonneg (q : ℝ)) hquadR]
  linarith [hdecomp, hcross]

open scoped Classical in
/-- **Peterfalvi (13.6), character-theoretic bound**: the norm lower bound
`∑_{x∈H#}|λ^{τ₁}(x)|² ≥ |S| − λ(1)²`, assembled from the (13.5) machinery.

For the irreducible `λ ∈ S` of degree `λ(1) = uq` induced from a linear character of `H = PC`
(so `‖λ‖² = 1`, `a = 1`, hence `κ = 1`), this chains the generic (13.5.b) decomposition
`sum_normSq_sharp_chi_decomp` (with `ζ = λ`, `χ = λ^{τ₁}`, `κ = 1`) into the arithmetic core
`caseB_lambda_norm_core`.  The character-theoretic content is exposed as explicit honest
hypotheses, each discharged from the (13.6) setup once it lands:
* `hvanish` — `λ` vanishes on `S − H` (induced from `H`, `H ⊴ S`);
* `hinner` — `(Res_H λ, α) = 0` (the `P`-kernel orthogonality of (13.5.a));
* `hχ` — the (13.5.a) point formula `λ^{τ₁} = λ + α` on `H#` (orthogonality from `S`-coherence);
* `hT` — `∑_S|λ|² = |S|` (`sum_normSq_eq_card_mul_inner` with `‖λ‖² = 1`);
* `hζ1`, `hcross` — `λ(1) = lam1` real and `Re(λ(1)·conj α(1)) = lam1·qb` (the `α(1) = qb`
  congruence of (13.5.a)+(1.10));
* `hinfl` — `(|P|−1)(qb)² ≤ ∑_{H#}|α|²` (Peterfalvi (13.5.c)); `hu` — `2u ≤ |P|−1` (13.2.c). -/
theorem caseB_lambda_norm_bound {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ α χ : S → ℂ) {Scard Pm1 u q : ℕ} {lam1 : ℝ} {b : ℤ}
    (hvanish : ∀ x : S, x ∉ H → ζ x = 0)
    (hinner : ∑ x ∈ Finset.univ.filter (· ∈ H), ζ x * (starRingEnd ℂ) (α x) = 0)
    (hχ : ∀ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, χ x = ζ x + α x)
    (hT : ∑ x : S, ‖ζ x‖ ^ 2 = (Scard : ℝ))
    (hζ1 : ‖ζ 1‖ ^ 2 = lam1 ^ 2)
    (hcross : (ζ 1 * (starRingEnd ℂ) (α 1)).re = lam1 * ((q : ℝ) * b))
    (hlam1 : lam1 = (u : ℝ) * q)
    (hinfl : (Pm1 : ℝ) * ((q : ℝ) * b) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖α x‖ ^ 2)
    (hu : 2 * u ≤ Pm1) :
    (Scard : ℝ) - lam1 ^ 2 ≤ ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖χ x‖ ^ 2 := by
  refine caseB_lambda_norm_core hlam1 ?_ hinfl hu
  rw [sum_normSq_sharp_chi_decomp H ζ α χ 1 hvanish hinner
    (by intro x hx; rw [hχ x hx, Complex.ofReal_one, one_mul]), hT, hζ1, hcross]
  ring

/-- **TI-subset `ρ`-map collapse** (the `χ = χ^ρ` bridge of Peterfalvi (13.5.a)): when the local
subgroups of a (7.1) datum are trivial (`H(a) = ⊥`, as for the TI-subset Dade construction
`H_sharp_dadeHypothesis`), the `ρ`-map is the identity on the support — `χ^ρ(a) = χ(a)` for `a ∈ A`.
Direct from the `chiRho` definition: the average `|H(a)|⁻¹ ∑_{x∈H(a)} χ(a·x)` over `H(a) = ⊥` is the
single term `χ(a·1) = χ(a)`.  This identifies the (13.5.a) point formula's left side with `χ`
itself,
so the (7.7.a) `chiRho_explicit_formula` decomposition reads off `χ(x)` on `H^#` directly. -/
theorem chiRho_eq_self_of_H_eq_bot {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    (H71 : OddOrder.Peterfalvi.S09.Hypothesis71 G A L)
    (hHbot : ∀ a : {a : G // a ∈ A}, H71.hyp.H a = ⊥)
    (χ : ClassFunction G ℂ) (a : L) (ha : (a : G) ∈ A) :
    H71.chiRho χ a = χ (a : G) := by
  rw [OddOrder.Peterfalvi.S09.Hypothesis71.chiRho, dif_pos ha, hHbot ⟨(a : G), ha⟩,
    Subgroup.card_bot, Nat.cast_one, inv_one, one_mul]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [show ((default : ↥(⊥ : Subgroup G)) : G) = 1 from
    Subgroup.mem_bot.mp (default : ↥(⊥ : Subgroup G)).2, mul_one]

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section GenericAlpha

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.a) point formula with a distinguished index (`a ≠ 0` form): the `P'`-non-kernel
middle coefficients vanish, leaving the `i₁`-term plus the `P'`-kernel tail. -/
theorem hypothesis76_point_formula [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (hHbot : ∀ a : {a : G // a ∈ A}, H76.hyp71.hyp.H a = ⊥)
    (P' : Subgroup ↥L) (χ : ClassFunction G ℂ)
    (i₁ : Fin (H76.n + 1)) (hi₁ : 0 < i₁)
    (hi₁ker : ¬ ((P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i₁)))
    (hmiddle : ∀ i : Fin (H76.n + 1), 0 < i → i ≠ i₁ →
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) →
      H76.cCoeff χ i = 0)
    (a : ↥L) (ha : (a : G) ∈ A) :
    χ (a : G) =
      (star (H76.cCoeff χ i₁) / H76.zetaNormSq i₁) * H76.zeta i₁ a
      + ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
            (fun i => (P' : Set ↥L) ⊆
              OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a := by
  classical
  have hbase : χ (a : G) = ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a :=
    (chiRho_eq_self_of_H_eq_bot H76.hyp71 hHbot χ a ha).symm.trans
      (OddOrder.Peterfalvi.S09.Hypothesis76.chiRho_explicit_formula H76 χ ha)
  rw [hbase, ← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr hi₁)]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Ioi 0).erase i₁)
      (fun i => (P' : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))]
  have hmid0 : ∑ i ∈ ((Finset.Ioi 0).erase i₁).filter (fun i =>
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_erase] at hi
    rw [hmiddle i (Finset.mem_Ioi.mp hi.1.2) hi.1.1 hi.2, star_zero, zero_div, zero_mul]
  have hi₁notin : i₁ ∉ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
      (fun i => (P' : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) := by
    rw [Finset.mem_filter]
    exact fun h => hi₁ker h.2
  rw [hmid0, add_zero, Finset.filter_erase, Finset.erase_eq_self.mpr hi₁notin]

end GenericAlpha

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Canonicalization.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Sharp-set sum transport** (subgroup-of form ↔ ambient form): for `K ≤ L`, a sum over the
nonidentity `K`-members *inside `↥L`* equals the sum over the ambient sharp `K^# ⊂ G`.  The
bridge between the (13.5)/(13.6) engines (stated inside the abstract ambient `↥S` with
`H.subgroupOf S`) and the (13.10) counting layer (stated over `sharpSubgroup K ⊂ G`). -/
theorem sum_apply_erase_one_filter_subgroupOf [Finite G] {M : Type*} [AddCommMonoid M]
    {K L : Subgroup G} [Fintype ↥L] (hKL : K ≤ L) (f : G → M) :
    ∑ x ∈ (Finset.univ.filter (· ∈ K.subgroupOf L)).erase 1, f ↑x
      = ∑ x ∈ (Set.toFinite (sharpSubgroup K)).toFinset, f x := by
  classical
  refine Finset.sum_bij' (fun x _ => (↑x : G))
    (fun y hy => (⟨y, hKL ((Set.Finite.mem_toFinset _).mp hy).1⟩ : ↥L)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, hxK⟩ := Finset.mem_erase.mp hx
    rw [Set.Finite.mem_toFinset]
    refine ⟨Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxK).2, ?_⟩
    intro h1
    rw [Set.mem_singleton_iff] at h1
    exact hx1 (Subtype.ext h1)
  · intro y hy
    obtain ⟨hyK, hy1⟩ := (Set.Finite.mem_toFinset _).mp hy
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr hyK⟩⟩
    intro h1
    exact hy1 (by simpa using congrArg (Subtype.val) h1)
  · intro x hx
    rfl
  · intro y hy
    rfl
  · intro x hx
    rfl

/-- **`2u ≤ |P| − 1`** (Peterfalvi (13.2.c) consequence): from the (13.2.e) bound
`u ≤ (p^q − 1)/(p − 1)` (`basic_structure`) and `p ≥ 3`, so `u ≤ (p^q−1)/2`. -/
theorem Hypothesis.two_mul_u_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : 2 * hyp.u ≤ hyp.p ^ hyp.q - 1 := by
  obtain ⟨-, -, -, -, hub, -⟩ := basic_structure hG hyp
  have hp3 := hyp.three_le_p
  have h1 : (hyp.p ^ hyp.q - 1) / (hyp.p - 1) ≤ (hyp.p ^ hyp.q - 1) / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h2 : (hyp.p ^ hyp.q - 1) / 2 * 2 ≤ hyp.p ^ hyp.q - 1 := Nat.div_mul_le_self _ _
  omega

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The chosen-base `(S, H^#)` family pins `ζ₀ = Ind_{PC}^S φ₀`.** -/
theorem H_sharp_hypothesis76_base_zeta_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.H.subgroupOf hyp.S)) :
    (H_sharp_hypothesis76_base hG hyp φ₀).zeta 0
      = ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) := by
  unfold H_sharp_hypothesis76_base
  exact OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeBase_zeta_zero _ _ _ _ _ _ _

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/HSharpChosenBase.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), chosen `𝒶₁` base for (13.5)**: the distinguished reducible
`μ`-column in `CharacterDegreeCore` supplies a `P`-nonkernel irreducible character `φ₀` of
`H = PC`.  Its induction is different from the irreducible `λ`; otherwise the column sum
would be irreducible. -/
theorem CharacterDegreeCore.exists_hSharpBase_ne_lambda [Finite G]
    {hyp : Hypothesis (G := G)} (core : CharacterDegreeCore hyp)
    (lam : LambdaClusterData hyp) :
    ∃ φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥(hyp.H.subgroupOf hyp.S),
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)) ∧
      ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda := by
  have := hyp.finiteG
  obtain ⟨j, δ, θ, hj, hδ, hθirr, hθ1, hθP, hμeq, hμτ⟩ :=
    core.mu_col_tau1_eta_col_one
  refine ⟨⟨θ, hθirr⟩, hθP, ?_⟩
  intro heq
  apply hyp.mu_colSum_not_irreducible j
  rw [hμeq, heq]
  exact lam.lambda_irreducible

open scoped FiniteInduce in
/-- **Peterfalvi (13.2.d)/(13.3), Core form**: `λ^{τ₁}` is a norm-one virtual
character.  The `P`-nonkernel witness stored in `LambdaClusterData` is exactly the guard needed
by the honest `CharacterDegreeCore` coherence fields. -/
theorem lambda_tau1_norm_one_core [Finite G] {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    core.tau1S lam.lambda ∈ ZIrr G ∧
      ClassFunction.inner (core.tau1S lam.lambda) (core.tau1S lam.lambda) = 1 ∧
      ClassFunction.inner lam.lambda lam.lambda = 1 := by
  have := hyp.finiteG
  obtain ⟨θ, hθirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  have hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  have hnorm : ClassFunction.inner lam.lambda lam.lambda = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨lam.lambda, lam.lambda_irreducible⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      ⟨lam.lambda, lam.lambda_irreducible⟩
    simpa using h
  refine ⟨?_, ?_, hnorm⟩
  · rw [hlamEq]
    exact core.tau1S_induce_mem_ZIrr θ hθirr hθP
  · rw [hlamEq, core.tau1S_inner_induce θ θ hθirr hθirr hθP hθP, ← hlamEq]
    exact hnorm

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3)/(13.5), chosen-base membership half**: `λ = Ind_H^S θ` occurs
in the (7.6) family based at `φ₀`.  It occurs at a positive index because the chosen base
induction is assumed distinct from `λ`; its `P`-nonkernel witness descends through induction. -/
theorem LambdaClusterData.exists_hSharpFamilyIndex_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    ∃ i₁ : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda := by
  classical
  obtain ⟨θ, hθirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  obtain ⟨i₁, hi₁⟩ :=
    (H_sharp_hypothesis76_base hG hyp φ₀).zeta_family_cover ⟨θ, hθirr⟩
  have heq : (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda := by
    rw [hi₁, hlamEq]
    congr!
  have hker : ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) := by
    intro hsub
    refine hx₀ker ?_
    have hx₀S : ((x₀ : ↥hyp.S)) ∈ hyp.P.subgroupOf hyp.S :=
      Subgroup.mem_subgroupOf.mpr hx₀P
    have hmem : ((x₀ : ↥hyp.S)) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) := by
      have h1 := hsub hx₀S
      rw [heq, hlamEq] at h1
      exact h1
    have hbridge := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (L := ↥hyp.S) (H := hyp.H.subgroupOf hyp.S) hθirr x₀.2 hmem
    rwa [show (⟨((x₀ : ↥hyp.S)), x₀.2⟩ : ↥(hyp.H.subgroupOf hyp.S)) = x₀ from rfl]
      at hbridge
  refine ⟨i₁, ?_, hker, heq⟩
  rw [Fin.pos_iff_ne_zero]
  intro hzero
  apply hφ₀ne
  rw [← heq, hzero, H_sharp_hypothesis76_base_zeta_zero]

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3)/(13.5), chosen-base distinguished index**: combines family
membership with the guarded (7.7.a) coefficient computation.  This is the honest
`CharacterDegreeCore`/`LambdaClusterData` replacement for the legacy `exists_lambda_index`. -/
theorem CharacterDegreeCore.exists_lambda_index_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    ∃ i₁ : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) i₁ = 1 ∧
      (∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) →
        (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) i = 0) := by
  obtain ⟨i₁, hpos, hker, heq⟩ := lam.exists_hSharpFamilyIndex_base hG φ₀ hφ₀ne
  obtain ⟨hc1, hmid⟩ := lambda_tau1_cCoeff_base hG core lam φ₀ hφ₀P hφ₀ne i₁ heq
  exact ⟨i₁, hpos, hker, heq, hc1, fun i _ hine hiP => hmid i hine hiP⟩

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/LambdaCorrection.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5.a), chosen-base orthogonality**: `λ` is orthogonal to its
`P`-kernel correction tail.  The abstract (7.6) orthogonality supplies the full `S`-sum;
`λ`'s chosen family member vanishes outside `H`, so this is the filtered sum used in (13.6). -/
theorem lambda_alphaFun_inner_zero_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
      lam.lambda x * (starRingEnd ℂ)
        (hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) x)) = 0 := by
  classical
  obtain ⟨i₁, -, hi₁ker, hi₁eq, -, -⟩ :=
    core.exists_lambda_index_base hG lam φ₀ hφ₀P hφ₀ne
  have hvanish : ∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → lam.lambda x = 0 := by
    intro x hx
    rw [← hi₁eq]
    exact (H_sharp_hypothesis76_base hG hyp φ₀).zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  have hext :
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
        lam.lambda x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
            (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) x))
        = ∑ x : ↥hyp.S, lam.lambda x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
            (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) x) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (· ∈ hyp.H.subgroupOf hyp.S)]
    have hzero : ∑ x ∈ Finset.univ.filter
        (fun x => ¬ x ∈ hyp.H.subgroupOf hyp.S),
        lam.lambda x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
            (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) x) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hvanish x (Finset.mem_filter.mp hx).2, zero_mul]
    rw [hzero, add_zero]
  rw [hext]
  have hfull := hypothesis76_zeta_inner_alphaFun_eq_zero
    (H_sharp_hypothesis76_base hG hyp φ₀) (hyp.P.subgroupOf hyp.S)
    (core.tau1S lam.lambda) i₁ hi₁ker
  rwa [hi₁eq] at hfull

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5.a,c), honest `λ` correction package**: choose the nonkernel base
from the reducible Core column, then assemble the point formula, orthogonality,
`α(1) = qb`, and inflation estimate for `λ^{τ₁}`.  The chosen base is internal to the proof;
the exported datum depends only on `CharacterDegreeCore` and `LambdaClusterData`. -/
theorem CharacterDegreeCore.exists_caseB_data_lambda_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    ∃ (α : ↥hyp.S → ℂ) (b : ℤ),
      (∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → lam.lambda x = 0) ∧
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
        lam.lambda x * (starRingEnd ℂ) (α x)) = 0 ∧
      (∀ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
        core.tau1S lam.lambda ↑x = lam.lambda x + α x) ∧
      α 1 = (hyp.q : ℂ) * (b : ℂ) ∧
      ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
            ‖α x‖ ^ 2 := by
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨φ₀, hφ₀P, hφ₀ne⟩ := core.exists_hSharpBase_ne_lambda lam
  obtain ⟨i₁, hi₁pos, hi₁ker, hi₁eq, hi₁c, hmiddle⟩ :=
    core.exists_lambda_index_base hG lam φ₀ hφ₀P hφ₀ne
  obtain ⟨-, -, hinnerLam⟩ := lambda_tau1_norm_one_core core lam
  obtain ⟨b, hb⟩ := core.exists_lambda_alphaFun_one_qb_base
    hG lam φ₀ hφ₀P hφ₀ne
  refine ⟨hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
    (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda), b, ?_, ?_, ?_, hb, ?_⟩
  · intro x hx
    rw [← hi₁eq]
    exact (H_sharp_hypothesis76_base hG hyp φ₀).zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  · exact lambda_alphaFun_inner_zero_base hG core lam φ₀ hφ₀P hφ₀ne
  · intro x hx
    obtain ⟨hx1, hxmem⟩ := Finset.mem_erase.mp hx
    have hxH : (↑x : G) ∈ hyp.H :=
      Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxmem).2
    have hxsharp : (↑x : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) := by
      refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxH, ?_⟩
      intro h1
      exact hx1 (Subtype.ext h1)
    have hpt := hypothesis76_point_formula (H_sharp_hypothesis76_base hG hyp φ₀)
      (fun _ => rfl) (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda)
      i₁ hi₁pos hi₁ker hmiddle x hxsharp
    rw [hpt, hi₁c]
    have hnorm1 : (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i₁ = 1 := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hi₁eq]
      exact hinnerLam
    rw [hnorm1, hi₁eq, star_one, div_one, one_mul]
    rfl
  · have hinfl := H_sharp_hypothesis76_base_alphaFun_inflation hG hyp φ₀
      (core.tau1S lam.lambda)
    rw [hb] at hinfl
    have hval : ‖(hyp.q : ℂ) * (b : ℂ)‖ ^ 2
        = ((hyp.q : ℝ) * (b : ℝ)) ^ 2 := by
      rw [norm_mul, mul_pow, Complex.norm_natCast, Complex.norm_intCast, sq_abs]
      ring
    rw [hval] at hinfl
    exact hinfl

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.6), honest Core form**:
`∑_{x∈H^#}|λ^{τ₁}(x)|² ≥ |S| - λ(1)²`, with `λ(1)=uq`.
The proof feeds the constructed (13.5) correction package into the abstract Case-B norm
engine, then transports the subgroup sum to the ambient sharp set. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    (Nat.card ↥hyp.S : ℝ) - ((hyp.u * hyp.q : ℕ) : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
          ‖core.tau1S lam.lambda x‖ ^ 2 := by
  classical
  obtain ⟨α, b, hvanish, hinner, hχ, hα1, hinfl⟩ :=
    core.exists_caseB_data_lambda_core hG lam
  obtain ⟨-, -, hinnerLam⟩ := lambda_tau1_norm_one_core core lam
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by
      rw [hyp.S_deriv_eq_PU]
      exact le_sup_right
    exact le_trans h1 (Subgroup.map_subtype_le _)
  have hHS : hyp.H ≤ hyp.S := by
    change hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]
      exact le_trans inf_le_left hUS
  have hT : ∑ x : ↥hyp.S, ‖lam.lambda x‖ ^ 2
      = ((Nat.card ↥hyp.S : ℕ) : ℝ) := by
    have h := sum_normSq_eq_card_mul_inner (H := ↥hyp.S) lam.lambda
    rw [hinnerLam, mul_one] at h
    exact_mod_cast h
  have hlamOne : lam.lambda 1 = ((hyp.u * hyp.q : ℕ) : ℂ) := lam.lambda_degree
  have hzetaOne : ‖lam.lambda 1‖ ^ 2
      = (((hyp.u * hyp.q : ℕ) : ℝ)) ^ 2 := by
    rw [hlamOne, Complex.norm_natCast]
  have hcross : (lam.lambda 1 * (starRingEnd ℂ) (α 1)).re
      = ((hyp.u * hyp.q : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) := by
    have hval : lam.lambda 1 * (starRingEnd ℂ) (α 1)
        = ((((hyp.u * hyp.q : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) : ℝ) : ℂ) := by
      rw [hlamOne, hα1, map_mul]
      push_cast [map_natCast, map_intCast]
      ring
    rw [hval, Complex.ofReal_re]
  have hlam1 : ((hyp.u * hyp.q : ℕ) : ℝ)
      = (hyp.u : ℝ) * (hyp.q : ℝ) := by
    push_cast
    ring
  have hu := hyp.two_mul_u_le hG
  have hengine : (Nat.card ↥hyp.S : ℝ) - ((hyp.u * hyp.q : ℕ) : ℝ) ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖core.tau1S lam.lambda ↑x‖ ^ 2 := by
    have h := caseB_lambda_norm_bound (S := ↥hyp.S) (hyp.H.subgroupOf hyp.S)
      (fun x => lam.lambda x) α (fun x => core.tau1S lam.lambda ↑x)
      (Scard := Nat.card ↥hyp.S) (Pm1 := hyp.p ^ hyp.q - 1)
      (u := hyp.u) (q := hyp.q) (lam1 := ((hyp.u * hyp.q : ℕ) : ℝ)) (b := b)
      hvanish (by convert hinner using 2)
      (fun x hx => hχ x (by convert hx using 2))
      hT hzetaOne hcross hlam1
      (by convert hinfl using 2; congr!) hu
    convert h using 2; congr!
  rwa [sum_apply_erase_one_filter_subgroupOf hHS
    (fun y => ‖core.tau1S lam.lambda y‖ ^ 2)] at hengine

end

end OddOrder.Peterfalvi.S15
