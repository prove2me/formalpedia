-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.frobenius_PU_of_field_repr
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:33:10.594045+00:00
-- url     : https://prove2.me/submissions/430b583b-0510-4f05-8596-3e6c2a6bd1be

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean
--   OddOrder/Peterfalvi/S16_G0Coprime.lean
--   OddOrder/Peterfalvi/S15_CaseBReducibleCoherence.lean
--   OddOrder/Peterfalvi/S15_CaseACoherence.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayerCore.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayer.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM
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
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_S
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_analytic_inequality_of_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_sSet_irr
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_forces_T_caseB_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseB_member
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseA
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S15_c_eq_one_of_analytic_inequality

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

/-- **`S`-instance chief-factor `q` identity**: the `(9.x)` chief-factor prime `data.q` of the
`S`-instance `toTypesIIIIIIVSetupS` is the type-`P` invariant `q = |W₁|`.  Extracted from
`u_le_cyclotomicQuotient` for reuse by the (13.3.b) dichotomy translations. -/
theorem Hypothesis.toTypesIIIIIIVSetupS_q_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
  change Nat.card ↥hyp.Sdata.W1 = hyp.q
  rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]

/-- **`S`-instance chief-factor prime identity**: the chief prime `chief.p = p`, forced by
`|P| = p^q = chief.p^q · |N|`.  Extracted from `u_le_cyclotomicQuotient`. -/
theorem Hypothesis.chiefFactorS_p_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    chief.p = hyp.p := by
  have := chief.N_normal
  have hHeq : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P := by
    change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [hHeq]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hyp.toTypesIIIIIIVSetupS_q_eq hG] at hquot
  have hsplitP := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplitP
  have hdvd : chief.p ∣ hyp.p ^ hyp.q :=
    dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') (hsplitP ▸ Dvd.intro _ rfl)
  exact (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
    (chief.p_prime.dvd_of_dvd_pow hdvd)

/-- **`S`-instance `u` identity**: the `U`-action image order `chars.u = |Ū| = [U : C_U(P)] = u`.
Extracted from `u_le_cyclotomicQuotient`; the (13.3.b) dichotomy uses it to transport the
`caseB_of_no_irreducible_sOf_H0Cprime` conclusion `chars.u = (p^q−1)/(p−1)` to `hyp.u`. -/
theorem Hypothesis.mkSection11CharacterDataS_u_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    (hyp.mkSection11CharacterDataS hG chief).u = hyp.u := by
  have hc0 : 0 < hyp.c := hyp.c_eq_card_C ▸ Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hc0 ?_
  have key : (hyp.mkSection11CharacterDataS hG chief).u
      * Nat.card ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
      = Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).U := by
    rw [← OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u (hyp.mkSection11CharacterDataS hG chief)]
    have h := Subgroup.index_mul_card
      ((OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief).subgroupOf
        (hyp.toTypesIIIIIIVSetupS hG).U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupS hG) chief)).toEquiv] at h
  rw [hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief, ← hyp.c_eq_card_C,
    show (hyp.toTypesIIIIIIVSetupS hG).U = hyp.U from hyp.Sdata_U_eq, hyp.card_U_eq_uc] at key
  exact key

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

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`H = PC` is abelian** (Peterfalvi (13.2.a,b)): `P` is (elementary) abelian
(`basic_structure`), `C ≤ U` is abelian (`S_U_commutative`), and `C` centralizes `P`
(`C = U ⊓ C_S(P)`), so the join is abelian (`isMulCommutative_sup_of_le_centralizer`).
The `habelian` input of the (13.7) Parseval bookkeeping. -/
theorem Hypothesis.H_mulCommutative [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : IsMulCommutative ↥hyp.H := by
  obtain ⟨-, -, hPel, -, -, -⟩ := basic_structure hG hyp
  have hPab : IsMulCommutative ↥hyp.P := ⟨⟨hPel.1⟩⟩
  have hCab : IsMulCommutative ↥hyp.C := by
    have hCU : hyp.C ≤ hyp.U := hyp.C_eq ▸ inf_le_left
    exact ⟨⟨fun a b => Subtype.ext (by
      have h := hyp.S_U_commutative.is_comm.comm
        (⟨(a : G), hCU a.2⟩ : ↥hyp.U) ⟨(b : G), hCU b.2⟩
      simpa using congrArg Subtype.val h)⟩⟩
  have hCP : hyp.C ≤ Subgroup.centralizer (hyp.P : Set G) := hyp.C_eq ▸ inf_le_right
  change IsMulCommutative ↥(hyp.P ⊔ hyp.C)
  rw [sup_comm]
  exact OddOrder.BG.Ch4.S15.isMulCommutative_sup_of_le_centralizer hCab hPab hCP

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

/-- **Peterfalvi (13.3.b), dichotomy glue** (§9-generic, issue 9013 gate 3): if the §9 family
`𝒮(H₀C')` contains **no** irreducible character, then case (9.7.b) holds
(a `CliffordCaseBData` — carrying the Singer facts `Ū` cyclic, `u ∣ (p^q−1)/(p−1)`, irreducible
action), with `C = ⊥` and the full value `u = (p^q − 1)/(p − 1)`.

Assembly of the sorry-free §9 endpoints: `clifford_dichotomy` splits into the two Clifford cases;
in case (a) the (9.8.c) witness (`caseA_character_counts` conjunct (c)) is an irreducible member
of `𝒮(H₀C) ⊆ 𝒮(H₀C')` (`sOf_antitone`, `C' ≤ C`) — contradicting the hypothesis; in case (b) the
(9.9.c) conjunct (d) of `caseB_character_counts` delivers both values.  This is the C=1/u-full
half of (13.3.b); the "case (9.7.b) holds"半 is the returned `CliffordCaseBData` itself.  Stated
generically over `M` so both the `S`- and `T`-instances (via `toTypesIIIIIIVSetupS` /
`toTypesIIIIIIVSetupT`) can cite it — the T-instance is the (13.4) θ-package's (13.3.b)-on-`T`
input (contrapositive form). -/
theorem caseB_of_no_irreducible_sOf_H0Cprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    ∃ _caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData chars,
      chars.C = ⊥ ∧ chars.u = (chief.p ^ data.q - 1) / (chief.p - 1) := by
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG chars with hA | hB
  · exfalso
    obtain ⟨caseA⟩ := hA
    obtain ⟨-, -, ⟨χ, hχmem, hχirr, -⟩, -⟩ :=
      OddOrder.Peterfalvi.S11.caseA_character_counts hG chars caseA
    exact hno ⟨χ,
      OddOrder.Peterfalvi.S11.sOf_antitone data
        (sup_le_sup_left chars.Cprime_le_C chief.H0) hχmem, hχirr⟩
  · obtain ⟨caseB⟩ := hB
    exact ⟨caseB,
      (OddOrder.Peterfalvi.S11.caseB_character_counts hG chars caseB).2.2.2 hno⟩

end CountingLayer

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **`T`-instance chief-factor `q` identity**: `data.q = p = |W₂|`.  Mirror of
`toTypesIIIIIIVSetupS_q_eq`. -/
theorem Hypothesis.toTypesIIIIIIVSetupT_q_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).q = hyp.p := by
  change Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).W1 = hyp.p
  rw [hyp.toTypesIIIIIIVSetupT_W1_eq hG hvd, ← hyp.p_eq_card_W2]

/-- **`T`-instance chief-factor prime identity**: `chief.p = q`, forced by
`|Q| = q^p = chief.p^p · |N|` (`card_Q_eq_qp`).  Mirror of `chiefFactorS_p_eq`. -/
theorem Hypothesis.chiefFactorT_p_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    chief.p = hyp.q := by
  have := chief.N_normal
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).H = hyp.q ^ hyp.p := by
    rw [show ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q from
      hyp.toTypesIIIIIIVSetupT_H_eq hG hvd]
    exact hyp.card_Q_eq_qp hG
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hyp.toTypesIIIIIIVSetupT_q_eq hG hvd] at hquot
  have hsplitQ := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplitQ
  have hdvd : chief.p ∣ hyp.q ^ hyp.p :=
    dvd_trans (dvd_pow_self chief.p hyp.p_prime.pos.ne') (hsplitQ ▸ Dvd.intro _ rfl)
  exact (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.q_prime).mp
    (chief.p_prime.dvd_of_dvd_pow hdvd)

/-- **Peterfalvi (13.2.b) at `T`, structure part**: `Q = T_F` is elementary abelian of
exponent `q`.

This is the `T`-side mirror of `Hypothesis.P_elementaryAbelian`.  It uses the general
type-`P`/type-II–IV setup on `T`, not the later (14.9) conclusion that `T` is type II:
`card_Q_eq_qp` makes the §9 chief kernel trivial, so the elementary-abelian chief factor
`Q/N` is `Q` itself, and `chiefFactorT_p_eq` identifies its prime with `q`. -/
theorem Hypothesis.Q_elementaryAbelian [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    IsElementaryAbelian hyp.q ↥hyp.Q := by
  classical
  have hvd : hyp.v * hyp.d ≠ 1 := hyp.vd_ne_one hG
  obtain ⟨chief, _⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupT hG hvd)
  have hN : chief.N = ⊥ := hyp.toTypesIIIIIIVSetupT_chief_N_eq_bot hG hvd chief
  have hp : chief.p = hyp.q := hyp.chiefFactorT_p_eq hG hvd chief
  have hEA : IsElementaryAbelian hyp.q ↥(hyp.toTypesIIIIIIVSetupT hG hvd).H := by
    have h := chief.quotient_elementaryAbelian
    rw [hp] at h
    exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot) h
  have hHeq : ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q :=
    hyp.toTypesIIIIIIVSetupT_H_eq hG hvd
  rwa [hHeq] at hEA

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_G0Coprime.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **The Fitting core `P = S_F` is nontrivial**: it contains `W₂` of prime order `p`. -/
theorem P_ne_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) : hyp.P ≠ ⊥ := by
  intro hbot
  have hW2 := OddOrder.Peterfalvi.S15.W2_le_P hG hyp
  rw [hbot, le_bot_iff] at hW2
  have hp1 : hyp.p = 1 := by rw [hyp.p_eq_card_W2, hW2, Subgroup.card_bot]
  exact hyp.p_prime.one_lt.ne' hp1

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S15_CaseBReducibleCoherence.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
/-- **`ℤ[𝒮]`-elements are supported in `A(S) ∪ {1}`** (issue 2035, the `zSpan`-closure of the
member-level honest (4.7) support fact `sSet_member_support_subset`).  Support is subadditive
under the lattice operations, so the union bound survives arbitrary `ℤ`-combinations. -/
theorem Hypothesis.zSpan_sSet_support_subset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {φ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupS hG))) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S ∪ {1} := by
  have : Fintype G := Fintype.ofFinite G
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hyp.sSet_member_support_subset hG hx
  | zero => simp
  | add x y _ _ hx hy =>
      exact (ClassFunction.support_add_subset x y).trans (Set.union_subset hx hy)
  | smul z x _ hx =>
      refine subset_trans ?_ hx
      rw [← Int.cast_smul_eq_zsmul ℂ z x]
      exact ClassFunction.support_smul_subset _ x

open OddOrder.Peterfalvi.S11 in
/-- **Degree-`0` elements of `ℤ[𝒮]` are `A(S)`-supported** (issue 2035, the (13.2.e)-input
support step for the `tau1S_apply_induce_sub` supply): a `ℤ`-combination of `𝒮`-members that
vanishes at `1` has its support inside the honest Dade support `A(S)` — the `{1}`-corner of
`zSpan_sSet_support_subset` is exactly the vanishing degree. -/
theorem Hypothesis.zSpan_sSet_degree_zero_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {φ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupS hG)))
    (hφ1 : φ (1 : ↥hyp.S) = 0) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
  have : Fintype G := Fintype.ofFinite G
  intro z hz
  rcases hyp.zSpan_sSet_support_subset hG hφ hz with h | h
  · exact h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact absurd hφ1 hz

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseACoherence.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c), the `μ`-column formula for `τ₁ = tau1S_ofHonest`** (issue 2035; Coq
`FTtypeP_coherence`, `PFsection13.v:347`): the (9.11)-coherent extension sends every reducible
`μ`-column sum `μ_j = ∑_i μ_{ij}` (`j ≠ 0`) to the aligned `η`-column sum `∑_i η_{ij}` — either
uniformly, or (the `p = 3` sign-flip exception) with a global negative sign and the two nonzero
columns swapped.  The `.choose_spec` of the pinned carrier `sSet_coherent_indS_A_pinned`; this is
the exact shape of the `CharacterDegreeData.mu_tau1_formula` field (`Machinery135`). -/
theorem Hypothesis.tau1S_ofHonest_muColumn_formula [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    (∀ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        = ∑ i : Fin hyp.q, hyp.eta i j) ∨
    (hyp.p = 3 ∧ ∀ j j' : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      j' ≠ ⟨0, hyp.p_prime.pos⟩ → j ≠ j' →
      hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        = -∑ i : Fin hyp.q, hyp.eta i j') :=
  (hyp.sSet_coherent_indS_A_pinned hG hnoV chief).choose_spec

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a)+(13.3.c), the distinguished `μ`-column for `τ₁ = tau1S_ofHonest`**
(issue 2035): a column `j ≠ 0` whose sum is induced from a linear character of `H = PC`
((13.3.a), `mu_j_isIndPC`) and whose `τ₁`-image is `±∑_i η_{i1}` — the (13.3.c) formula routed to
the `η`-column `1` (`j = 1, δ = 1` in the clean branch; the `p = 3` sign-flip exception takes
`j = 2, δ = -1`).  This is the honest supply of the `CharacterDegreeData.mu_col_tau1_eta_col_one`
field. -/
theorem Hypothesis.tau1S_ofHonest_mu_col_eta_col_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    ∃ (j : Fin hyp.p) (δ : ℤ) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      j ≠ ⟨0, hyp.p_prime.pos⟩ ∧
      (δ = 1 ∨ δ = -1) ∧
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
      (∑ i : Fin hyp.q, hyp.mu i j) = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
      hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        = (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ := by
  classical
  have := hyp.finiteG
  have hp1 : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  rcases hyp.tau1S_ofHonest_muColumn_formula hG hnoV chief with hclean | ⟨hp3, hflip⟩
  · -- clean branch: `j = 1`, `δ = 1`
    obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG ⟨1, hyp.p_prime.one_lt⟩ hp1
    exact ⟨⟨1, hyp.p_prime.one_lt⟩, 1, θ, hp1, Or.inl rfl, hθirr, hθ1, hθeq,
      by rw [hclean ⟨1, hyp.p_prime.one_lt⟩ hp1]; push_cast; rw [one_smul]⟩
  · -- `p = 3` sign-flip branch: `j = 2`, `δ = -1`
    have h2lt : 2 < hyp.p := by omega
    have hj2 : (⟨2, h2lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
      intro h; exact absurd (congrArg Fin.val h) (by norm_num)
    have hne : (⟨2, h2lt⟩ : Fin hyp.p) ≠ ⟨1, hyp.p_prime.one_lt⟩ := by
      intro h; exact absurd (congrArg Fin.val h) (by norm_num)
    obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG ⟨2, h2lt⟩ hj2
    refine ⟨⟨2, h2lt⟩, -1, θ, hj2, Or.inr rfl, hθirr, hθ1, hθeq, ?_⟩
    rw [hflip ⟨2, h2lt⟩ ⟨1, hyp.p_prime.one_lt⟩ hj2 hp1 hne]
    push_cast
    rw [neg_one_smul]

open scoped FiniteInduce in
/-- **Type-alignment probe for the (13.3) `τ₁` route** (issue 2035 step 4 verification): confirms
`coherent_H0Cprime_S` obtains and its `.extension` is definitionally `tau1S_ofHonest`, of the
expected `IntegralCharacterMap ↥S G` type; and that `extends_on_supported` gives
`τ₁ φ = Ind_S^G φ` on the supported span (`tau1S_apply_induce` on the family) — the input to the
(13.3) `tau1S_apply_induce_sub` / `tau1S_inner_induce` / `tau1S_induce_mem_ZIrr` fields. -/
theorem Hypothesis.tau1S_ofHonest_extends_on_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (φ : ClassFunction ↥hyp.S ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport) :
    hyp.tau1S_ofHonest hG hnoV chief φ = ClassFunction.induce hyp.S φ := by
  have h := (hyp.coherent_H0Cprime_S hG hnoV chief).extends_on_supported φ hφ
  -- `.extension φ = chars.tau φ = indS φ = Ind_S^G φ`
  simpa [Hypothesis.tau1S_ofHonest, Hypothesis.mkSection11CharacterDataS_honest,
    Hypothesis.indS_apply] using h

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ isometry on the `H`-induced family** (issue 2035 step 5a): `τ₁ = tau1S_ofHonest`
preserves inner products of `Ind_{PC}^S θ` for irreducible `θ` of `H = PC` with `P ⊄ Ker θ`.  From
the coherence field `extension_inner_eq` (isometric on all of `ℤ[𝒮]`) together with the family
membership `induce_H_mem_zSpan_S`.  This is the honest engine for the `CharacterDegreeData`
`tau1S_inner_induce` field (with the `P ⊄ Ker` hypothesis the (13.3) consumers actually satisfy —
`μ_j`, `λ` all have `P ⊄ Ker`). -/
theorem Hypothesis.tau1S_ofHonest_inner_induce [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθ' : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hθ'P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ')) :
    ClassFunction.inner
        (hyp.tau1S_ofHonest hG hnoV chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ))
        (hyp.tau1S_ofHonest hG hnoV chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'))
      = ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') := by
  exact (hyp.coherent_H0Cprime_S hG hnoV chief).extension_inner_eq _ _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)
    (hyp.induce_H_mem_zSpan_S hG chief θ' hθ' hθ'P)

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ sends the `H`-induced family into `ℤ[Irr G]`** (issue 2035 step 5a): for
irreducible `θ` of `H = PC` with `P ⊄ Ker θ`, `τ₁ (Ind_{PC}^S θ) ∈ ℤ[Irr G]`.  From the coherence
field `extension_mem_ZIrr` (virtual-character codomain on all of `ℤ[𝒮]`) and the family membership
`induce_H_mem_zSpan_S`.  Honest engine for the `CharacterDegreeData` `tau1S_induce_mem_ZIrr`
field. -/
theorem Hypothesis.tau1S_ofHonest_induce_mem_ZIrr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    hyp.tau1S_ofHonest hG hnoV chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) ∈ ZIrr G :=
  (hyp.coherent_H0Cprime_S hG hnoV chief).extension_mem_ZIrr _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)

open scoped FiniteInduce in
/-- **(13.2.e)+(7.2), the τ₁-extension semantics on `H`-induced differences** (issue 2035, the
honest supply for the `CharacterDegreeData.tau1S_apply_induce_sub` field): for irreducible
characters `θ, θ'` of `H = PC` with `P ⊄ Ker` (the guard the (13.5) proof carries — Peterfalvi
converts `(ζ_i − ζ_0)^{τ}` to `Ind_S^G` *only* for the `𝒮₁`-members `i ≤ n`, the `P`-kernel side
staying as the unknown `α`), `τ₁` agrees with `Ind_S^G` on the difference `Ind θ − Ind θ'`.

Assembly: both inductions lie in `ℤ[𝒮]` (`induce_H_mem_zSpan_S`, the (1.5.a) membership); `H` is
abelian ((13.2.a)) so both are degree `uq` and the difference vanishes at `1`; hence the
difference is `A(S)`-supported (`zSpan_sSet_degree_zero_support`) and `extends_on_supported`
evaluates `τ₁` as `Ind_S^G` there. -/
theorem Hypothesis.tau1S_ofHonest_apply_induce_sub [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθ' : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hθ'P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ')) :
    hyp.tau1S_ofHonest hG hnoV chief
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
          - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
      = ClassFunction.induce hyp.S
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
            - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') := by
  have := hyp.finiteG
  -- `ℤ[𝒮]` membership of both inductions ((1.5.a))
  have hmem := hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP
  have hmem' := hyp.induce_H_mem_zSpan_S hG chief θ' hθ' hθ'P
  have hsub : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
      ∈ OddOrder.Peterfalvi.S07.zSpan
          (OddOrder.Peterfalvi.S11.sSet (hyp.toTypesIIIIIIVSetupS hG)) :=
    Submodule.sub_mem _ hmem hmem'
  -- `H = PC` abelian ((13.2.a)): both inducing characters are linear, the difference has degree 0
  have hHcomm : IsMulCommutative ↥(hyp.H.subgroupOf hyp.S) := by
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe (show hyp.H ≤ hyp.S from hyp.H_le_S)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hθ1 : θ 1 = 1 :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative hθ
  have hθ'1 : θ' 1 = 1 :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative hθ'
  have hdeg : (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') (1 : ↥hyp.S) = 0 := by
    rw [ClassFunction.sub_apply,
      OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
      OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, hθ'1, sub_self]
  -- `A(S)`-support of the degree-0 difference, then the (13.2.d) extension evaluates as `Ind`
  exact hyp.tau1S_ofHonest_extends_on_supported hG hnoV chief _
    ⟨hsub, hyp.zSpan_sSet_degree_zero_support hG hsub hdeg⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁`-images of `ℤ[𝒮 ∩ Irr S]` are orthogonal to the `η`-grid** (Peterfalvi
(4.1)+(5.3.b), issue 2035): span induction over the (5.3.b) crux
`coherentIndS_image_inner_eta_eq_zero` — `τ₁` is `ℤ`-linear and the inner product is linear in
the first slot, so the member-level grid-orthogonality extends to the integral span of the
irreducible members. -/
theorem Hypothesis.tau1S_ofHonest_zSpanIrr_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q) (j : Fin hyp.p)
    {φ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan
      {ψ : ClassFunction ↥hyp.S ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) ∧
        OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ}) :
    ClassFunction.inner (hyp.tau1S_ofHonest hG hnoV chief φ) (hyp.eta i j) = 0 := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  induction hφ using Submodule.span_induction with
  | mem ζ hζ =>
      exact coherentIndS_image_inner_eta_eq_zero hG hnoV hyp
        (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG))
        (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG))
        (fun ζ' hζ' => by
          rw [show ζ' - (ζ' : ClassFunction ↥hyp.S ℂ).conj
              = -((ζ' : ClassFunction ↥hyp.S ℂ).conj - ζ') from (neg_sub _ _).symm,
            ClassFunction.support_neg]
          exact hyp.sSet_member_conjDiff_supported hG hζ')
        (hyp.coherent_H0Cprime_S hG hnoV chief) hζ.1 hζ.2 i j
  | zero => rw [map_zero, OddOrder.RepresentationTheory.ClassFunction.inner_zero_left]
  | add x y _ _ hx hy =>
      rw [map_add, OddOrder.RepresentationTheory.ClassFunction.inner_add_left, hx, hy, add_zero]
  | smul z x _ hx =>
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ z,
        OddOrder.RepresentationTheory.ClassFunction.inner_smul_left, hx, mul_zero]

open scoped FiniteInduce in
/-- **(4.1)+(5.3.b) honest supply for the `tau1S_induce_inner_eta` field** (issue 2035/9094): for
an irreducible `θ ∈ Irr H` (`H = PC`, `P ⊄ Ker θ`) whose induction `Ind_{PC}^S θ` is irreducible,
the `τ₁`-image is orthogonal to the whole `η`-grid.  Composition of the `ℤ[𝒮 ∩ Irr S]`
membership (`induce_H_mem_zSpan_sSet_irr`, Coq `S1cases` irreducible branch) with the span-level
grid orthogonality (`tau1S_ofHonest_zSpanIrr_inner_eta`). -/
theorem Hypothesis.tau1S_ofHonest_induce_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q) (j : Fin hyp.p)
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) :
    ClassFunction.inner (hyp.eta i j)
      (hyp.tau1S_ofHonest hG hnoV chief
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0 := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    hyp.tau1S_ofHonest_zSpanIrr_inner_eta hG hnoV chief i j
      (hyp.induce_H_mem_zSpan_sSet_irr hG θ hθ hθP hind),
    star_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁`-images of the full lattice `ℤ[𝒮]` are orthogonal to the `η`-column `0`**
(Peterfalvi (4.1)+(5.3.b) + (13.3.c), issue 2035): span induction over the *mixed* family —
an irreducible member is grid-orthogonal by the (5.3.b) crux; a reducible member is a
`μ`-column (`sSet_reducible_eq_muColumnSum`) whose `τ₁`-image is a (signed) *nonzero*-column
`η`-sum (`tau1S_ofHonest_muColumn_formula`), orthogonal to column `0` by the grid
orthonormality. -/
theorem Hypothesis.tau1S_ofHonest_zSpan_inner_eta_col_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q)
    {φ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupS hG))) :
    ClassFunction.inner (hyp.tau1S_ofHonest hG hnoV chief φ)
      (hyp.eta i ⟨0, hyp.p_prime.pos⟩) = 0 := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  induction hφ using Submodule.span_induction with
  | mem ζ hζ =>
      by_cases hζirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter ζ
      · -- irreducible member: full grid orthogonality by the (5.3.b) crux
        exact coherentIndS_image_inner_eta_eq_zero hG hnoV hyp
          (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG))
          (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG))
          (fun ζ' hζ' => by
            rw [show ζ' - (ζ' : ClassFunction ↥hyp.S ℂ).conj
                = -((ζ' : ClassFunction ↥hyp.S ℂ).conj - ζ') from (neg_sub _ _).symm,
              ClassFunction.support_neg]
            exact hyp.sSet_member_conjDiff_supported hG hζ')
          (hyp.coherent_H0Cprime_S hG hnoV chief) hζ hζirr i ⟨0, hyp.p_prime.pos⟩
      · -- reducible member: a nonzero `μ`-column, sent by (13.3.c) into a nonzero `η`-column
        obtain ⟨j, hj, rfl⟩ := hyp.sSet_reducible_eq_muColumnSum hG hζ hζirr
        rcases hyp.tau1S_ofHonest_muColumn_formula hG hnoV chief with hclean | ⟨-, hflip⟩
        · rw [hclean j hj, OddOrder.RepresentationTheory.inner_sum_left]
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [hyp.eta_orthonormal l i j ⟨0, hyp.p_prime.pos⟩, if_neg (fun h => hj h.2)]
        · have h2lt : 2 < hyp.p := by have := hyp.three_le_p; omega
          set j1 : Fin hyp.p := ⟨1, hyp.p_prime.one_lt⟩ with hj1
          set j2 : Fin hyp.p := ⟨2, h2lt⟩ with hj2
          have hj10 : j1 ≠ ⟨0, hyp.p_prime.pos⟩ := by
            intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          have hj20 : j2 ≠ ⟨0, hyp.p_prime.pos⟩ := by
            intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          -- route through the other nonzero column `j' ≠ 0, j' ≠ j`
          obtain ⟨j', hj'0, hjj'⟩ : ∃ j' : Fin hyp.p,
              j' ≠ ⟨0, hyp.p_prime.pos⟩ ∧ j ≠ j' := by
            rcases eq_or_ne j j1 with rfl | hne1
            · exact ⟨j2, hj20, fun h => absurd (congrArg Fin.val h) (by norm_num)⟩
            · exact ⟨j1, hj10, hne1⟩
          rw [hflip j j' hj hj'0 hjj',
            OddOrder.RepresentationTheory.ClassFunction.inner_neg_left,
            OddOrder.RepresentationTheory.inner_sum_left]
          rw [Finset.sum_eq_zero fun l _ => by
            rw [hyp.eta_orthonormal l i j' ⟨0, hyp.p_prime.pos⟩, if_neg (fun h => hj'0 h.2)]]
          exact neg_zero
  | zero => rw [map_zero, OddOrder.RepresentationTheory.ClassFunction.inner_zero_left]
  | add x y _ _ hx hy =>
      rw [map_add, OddOrder.RepresentationTheory.ClassFunction.inner_add_left, hx, hy, add_zero]
  | smul z x _ hx =>
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ z,
        OddOrder.RepresentationTheory.ClassFunction.inner_smul_left, hx, mul_zero]

open scoped FiniteInduce in
/-- **(4.1)+(5.3.b)+(13.3.c) honest supply for the `tau1S_induce_inner_eta_col_zero` field**
(issue 2035/9094): for *any* irreducible `θ ∈ Irr H` (`H = PC`, `P ⊄ Ker θ`) — the induction
`Ind_{PC}^S θ` may be irreducible or a `μ`-column — the `τ₁`-image is orthogonal to the
`η`-column `0`.  Composition of the `ℤ[𝒮]` membership (`induce_H_mem_zSpan_S`) with the
mixed-family column-`0` orthogonality (`tau1S_ofHonest_zSpan_inner_eta_col_zero`). -/
theorem Hypothesis.tau1S_ofHonest_induce_inner_eta_col_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q)
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.inner (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
      (hyp.tau1S_ofHonest hG hnoV chief
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0 := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    hyp.tau1S_ofHonest_zSpan_inner_eta_col_zero hG hnoV chief i
      (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP),
    star_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a) with the `P`-witness** (issue 2035 更新 #22, the guard the (13.5)
consumers thread): the inducing linear character `θ` of the nonzero `μ`-column sum
`μ_j = Ind_{PC}^S θ` has `P ⊄ Ker θ` — i.e. `μ_j ∈ 𝒮₁` in the sense of (13.5).

**Proof.**  `mu_j_isIndPC` supplies `θ`; if `P ⊆ Ker θ` then `P ⊆ Ker μ_j` by the elementary
half of (1.6.a) (`subsetCharacterKernel_induce_of_subgroupOf`, `P ⊴ S`).  But `μ_j ∈ 𝒮(H₀)`
(`mu_colSum_mem_sOf_H0`) is induced from an `S'`-source `χ ∈ 𝒳` with `P ⊄ Ker χ`, and the
converse of (1.6.a) ([Is] 2.21, `mem_characterKernel_of_mem_characterKernel_induce`, `S' ⊴ S`)
pushes `P ⊆ Ker μ_j` down to `P ⊆ Ker χ` — contradiction. -/
theorem Hypothesis.mu_j_isIndPC_not_ker [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
        (∑ i : Fin hyp.q, hyp.mu i j)
          = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
        ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
            Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel θ) := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨θ, hθirr, hθ1, hμeq⟩ := hyp.mu_j_isIndPC hG j hj
  refine ⟨θ, hθirr, hθ1, hμeq, fun hker => ?_⟩
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  -- the `S'`-level source: `μ_j = Ind_{HU}^S χ`, `χ ∈ 𝒳` (so `P ⊄ Ker χ`)
  obtain ⟨χ, hχ, hμeq'⟩ := OddOrder.Peterfalvi.S11.mem_sOf.mp
    (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)
  let : Fintype ↥(OddOrder.Peterfalvi.S11.huSub data) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(OddOrder.Peterfalvi.S11.huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hHUnorm : (OddOrder.Peterfalvi.S11.huSub data).Normal := by
    rw [OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data]
    infer_instance
  -- `P ⊴ S`, realised in `↥S`
  have hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
    have hPle : hyp.P ≤ hyp.S := by
      rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr ?_
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hPH : hyp.P.subgroupOf hyp.S ≤ hyp.H.subgroupOf hyp.S :=
    Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
  -- (1.6.a) forward: `P ⊆ Ker θ` pushes up to `P ⊆ Ker μ_j`
  have hkerInd : OddOrder.Peterfalvi.S03.SubsetCharacterKernel
      ((hyp.P.subgroupOf hyp.S : Subgroup ↥hyp.S) : Set ↥hyp.S)
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) :=
    OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf hPH θ hker
  -- rewrite the induced character as the `S'`-stage induction
  have hInd_eq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      = ClassFunction.induce (OddOrder.Peterfalvi.S11.huSub data)
          (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ) := by
    rw [← hμeq, hμeq']
    exact OddOrder.Peterfalvi.S11.induceHU_eq_induce data _
  -- contradict `χ ∈ 𝒳`: `P (in HU) ⊆ Ker χ`
  apply hχ.1
  intro x hx
  have hxP : (x : ↥hyp.S) ∈ hyp.P.subgroupOf hyp.S := by
    have hx' : x ∈ (data.H.subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data) := hx
    have hPeq : data.H = hyp.P := by
      change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
    rw [hPeq] at hx'
    exact Subgroup.mem_subgroupOf.mp hx'
  have hxkerInd : (x : ↥hyp.S) ∈ OddOrder.Peterfalvi.S03.characterKernel
      (ClassFunction.induce (OddOrder.Peterfalvi.S11.huSub data)
        (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ)) := by
    rw [← hInd_eq]
    exact hkerInd hxP
  have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
    χ.isIrreducible x.2 hxkerInd
  simpa using h

open scoped FiniteInduce in
/-- **The λ-free core producer** (issue 9094 RULING 案 A): every field of
`CharacterDegreeCore` from the landed engines — `τ₁ = tau1S_ofHonest` with its five guarded
field supplies, the (13.3.a) `𝒮₁`-witnessed `μ`-facts (`mu_j_isIndPC_not_ker`,
`tau1S_ofHonest_mu_col_eta_col_one`), the (13.3.c) `S`-side signs (`delta_eq_one_S`; the
δ′-half is restate-dropped from the field, issue 2035 #92 — supply stays in
`deltaPrime_eq_one_T`), and the (13.3.c) column formula
(`tau1S_ofHonest_muColumn_formula`). -/
noncomputable def Hypothesis.characterDegreeCore [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    CharacterDegreeCore hyp where
  tau1S := hyp.tau1S_ofHonest hG hnoV chief
  tau1T := hyp.indT
  tau1S_apply_induce_sub := fun θ θ' hθ hθ' hθP hθ'P =>
    hyp.tau1S_ofHonest_apply_induce_sub hG hnoV chief θ θ' hθ hθ' hθP hθ'P
  tau1S_inner_induce := fun θ θ' hθ hθ' hθP hθ'P =>
    hyp.tau1S_ofHonest_inner_induce hG hnoV chief θ θ' hθ hθ' hθP hθ'P
  tau1S_induce_mem_ZIrr := fun θ hθ hθP =>
    hyp.tau1S_ofHonest_induce_mem_ZIrr hG hnoV chief θ hθ hθP
  tau1S_induce_inner_eta := fun i j θ hθ hθP hind =>
    hyp.tau1S_ofHonest_induce_inner_eta hG hnoV chief i j θ hθ hθP hind
  tau1S_induce_inner_eta_col_zero := fun i θ hθ hθP =>
    hyp.tau1S_ofHonest_induce_inner_eta_col_zero hG hnoV chief i θ hθ hθP
  mu_col_tau1_eta_col_one := by
    obtain ⟨j, δ, θold, hj, hδ, -, -, -, hform⟩ :=
      hyp.tau1S_ofHonest_mu_col_eta_col_one hG hnoV chief
    obtain ⟨θ, hθirr, hθ1, hμeq, hθP⟩ := hyp.mu_j_isIndPC_not_ker hG j hj
    exact ⟨j, δ, θ, hj, hδ, hθirr, hθ1, hθP, hμeq, hform⟩
  mu_j_linear_induced := fun j hj => by
    obtain ⟨θ, hθirr, hθ1, hμeq, hθP⟩ := hyp.mu_j_isIndPC_not_ker hG j hj
    exact ⟨θ, hθirr, hθ1, hθP, hμeq⟩
  delta_eq_one := fun j => hyp.delta_eq_one_S hG j
  mu_tau1_formula := hyp.tau1S_ofHonest_muColumn_formula hG hnoV chief

/-- **The λ-free core, unconditionally** (issue 9094 RULING 案 A): `CharacterDegreeCore` is
inhabited for every (13.1) hypothesis — the (12.x) no-type-V fact supplies `hnoV`, and a chief
factor datum always exists. -/
theorem Hypothesis.characterDegreeCore_nonempty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (CharacterDegreeCore hyp) := by
  have := hyp.finiteG
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
    (hyp.toTypesIIIIIIVSetupS hG)
  exact ⟨hyp.characterDegreeCore hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG) chief⟩

open scoped FiniteInduce in
/-- **The conditional λ-cluster producer** (issue 9094 RULING 案 A, the (13.3.b) conditional
branch): a linear `θ ∈ Irr H` (`H = PC`) with `P ⊄ Ker θ` whose induction `Ind_{PC}^S θ` is
irreducible packages into `LambdaClusterData` — the degree is `[S:H]·1 = uq`
(`H_index_eq_uq`). -/
theorem Hypothesis.lambdaClusterData_of_irr_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ) (hθ1 : θ 1 = 1)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) :
    Nonempty (LambdaClusterData hyp) := by
  have := hyp.finiteG
  refine ⟨⟨ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ, hind, ?_, θ, hθ, hθ1, rfl, ?_⟩⟩
  · rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one,
      hyp.H_index_eq_uq hG]
  · obtain ⟨x, hxP, hxker⟩ := Set.not_subset.mp hθP
    exact ⟨x, Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxP), hxker⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayerCore.lean =====
namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

section

/-- **Peterfalvi (13.12), Core form**: the centralizer parameter `c` is one, using the
Core analytic inequality instead of the legacy norm-cascade carrier. -/
theorem CharacterDegreeCore.c_eq_one_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    hyp.c = 1 := by
  exact c_eq_one_of_analytic_inequality hG hyp
    (core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm pins)

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The no-λ (Galois) branch of the `S`-side (13.3.b) facts** (issue 9094 RULING §2, faithful
bridging — introduced sorried, since proved): if `𝒮` contains no `uq`-degree `PC`-induced
irreducible (`¬ LambdaWitness`),
then by Pf (13.3.b) `M = S` is in case (9.7.b) with `C = ⊥` and `u = (p^q−1)/(p−1)` — the Galois
case.

Assembled from the §9-generic `caseB_of_no_irreducible_sOf_H0Cprime` (sorry-free) through the
S15↔S11 `Section11CharacterData` SOf-identification: an irreducible member of the `S`-instance
family `𝒮(H₀ ⊔ C')` is (13.3.a-style) a `uq`-degree `PC`-linear induced irreducible, i.e. a
`LambdaWitness`, and the `chars.C`/`chars.u` conclusion transports to `hyp.C`/`hyp.u`
(`toTypesIIIIIIVSetupS_cSub_eq_C`).  That identification is the deep (13.3.b) forward bridge
(S15↔S11, multi-session); until it lands this is the honest, precisely-named gate. -/
theorem S_caseB_facts_no_lambda [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hnolam : ¬ LambdaWitness hyp) :
    hyp.C = ⊥ ∧ hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1) := by
  have := hyp.finiteG
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
  -- **(13.3.b) forward, the one isolated genuine gate**: an irreducible member of the `S`-instance
  -- family `𝒮(H₀ ⊔ C')` is a `uq`-degree `PC`-linear induced irreducible — a `LambdaWitness`.
  -- (The reducible members are `Ind_{HC}` linear by `caseB_reducible_sOf_H0_isIndHC`; the
  -- irreducible ones — the `λ`-candidates — need the (13.3.a)-for-irr characterization, the
  -- multi-session S15↔S11 assembly.)
  have hbridge : ∀ χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ → LambdaWitness hyp := by
    intro χ _hχmem _hχirr
    -- `set`-free case split: a `set data`/`set chars` here would split the (externally obtained)
    -- `chief` into a folded copy plus a stray `chief✝`, desyncing `_hχmem` from `caseB`.  Both
    -- branches are `set`-free standalone witnesses (`lambdaWitness_of_caseA` / `_of_caseB_member`),
    -- each doing its own `let data` internally, so hbridge passes one pristine `chief`.
    rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataS hG chief) with hA | hB
    · -- **caseA**: a `LambdaWitness` exists unconditionally (ignore `χ`) — the (9.8.c) degree-`qu`
      -- irreducible `Ind_{HU}^S(Ind_{HC}(hcPsi θ̄))` is `Ind_{PC}^S(linear irr)`.
      obtain ⟨caseA⟩ := hA
      exact lambdaWitness_of_caseA hG hyp chief caseA
    · -- **caseB** (Singer/Galois, `U` irreducible on `H̄`): the given irreducible `χ = Ind_{HU} ζ`
      -- (`ζ ∈ 𝒳(H₀C')`) is `Ind_{HC}(hcPsiPair θ̄ λ)` for a linear pair character
      -- (`caseB_xiOf_H0Cprime_eq_induce_hcPsiPair`); `lambdaWitness_of_caseB_member` flattens and
      -- transports it to the `Ind_{PC}(linear irr)` = `LambdaWitness` shape.
      obtain ⟨caseB⟩ := hB
      exact lambdaWitness_of_caseB_member hG hyp chief caseB _hχmem _hχirr
  have hno : ¬ ∃ χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    fun ⟨χ, hmem, hirr⟩ => hnolam (hbridge χ hmem hirr)
  obtain ⟨-, hCbot, hufull⟩ :=
    caseB_of_no_irreducible_sOf_H0Cprime hG
      (hyp.mkSection11CharacterDataS hG chief) hno
  refine ⟨?_, ?_⟩
  · -- `chars.C = cSub = hyp.C` (`toTypesIIIIIIVSetupS_cSub_eq_C`)
    rw [← hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]
    exact hCbot
  · -- transport `chars.u = (chief.p^data.q − 1)/(chief.p − 1)` to `hyp.u = (p^q − 1)/(p − 1)`
    rw [← hyp.mkSection11CharacterDataS_u_eq hG chief, hufull, hyp.chiefFactorS_p_eq hG chief,
      hyp.toTypesIIIIIIVSetupS_q_eq hG]

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.b) dichotomy, the `S`-side keystone producer** (issue 9094 RULING 案 A/§2):
either `𝒮` contains the honest λ-cluster (`Nonempty (LambdaClusterData hyp)`), or `M = S` is in
the Galois case (`C = ⊥`, `u = (p^q−1)/(p−1)`).  This is the producer every λ-independent
consumer of the legacy `character_degree_analysis` threads: the λ-branch supplies the
`LambdaClusterData` (against the unconditional `CharacterDegreeCore`), the no-λ branch supplies
the (13.10)-arithmetic inputs `C = ⊥ ∧ u = full`.

The case-split is `LambdaWitness hyp` (`Classical.em`): the λ-branch is
`lambdaClusterData_of_irr_witness`, the no-λ branch is `S_caseB_facts_no_lambda`. -/
theorem lambdaCluster_or_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (LambdaClusterData hyp) ∨
      (hyp.C = ⊥ ∧ hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  by_cases hlam : LambdaWitness hyp
  · obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := hlam
    exact Or.inl (hyp.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind)
  · exact Or.inr (S_caseB_facts_no_lambda hG hyp hlam)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayer.lean =====
namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

section

/-- **Peterfalvi (13.12), honest dichotomy form**: `c = 1`.

This is the unconditional replacement for the legacy monolithic character-degree carrier.
If the (13.3.b) λ-cluster exists, `lambda_forces_T_caseB_core` supplies the `T`-side case-B
facts and the general type-`P` theorem `Q_elementaryAbelian` supplies the commutativity needed
by the Core analytic endpoint.  This avoids the circular route through the later (14.9)
`T_typeII`, whose character proof itself consumes (13.12).  If no λ-cluster exists, the
faithful Galois branch already gives `C = ⊥`. -/
theorem Hypothesis.c_eq_one_of_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) :
    hyp.c = 1 := by
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  rcases lambdaCluster_or_caseB hG hyp with hlam | ⟨hCbot, _hu⟩
  · obtain ⟨lam⟩ := hlam
    obtain ⟨hD, hv, _hQ⟩ := lambda_forces_T_caseB_core hG core lam pins
    have hQcomm : IsMulCommutative ↥hyp.Q :=
      IsMulCommutative.of_comm (hyp.Q_elementaryAbelian hG).comm
    exact core.c_eq_one_of_caseB_facts hG lam hD hv hQcomm pins
  · exact hyp.c_eq_card_C.trans (Subgroup.card_eq_one.mpr hCbot)

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **(14.7) `hPU_disj` input**: `P ∩ U = 1`.  Since `P` is elementary abelian it
centralizes itself, so `P ⊓ U ≤ U ⊓ C_G(P) = C = 1` by (13.12) `c = 1`, supplied by
the Core λ-dichotomy endpoint. -/
theorem P_inf_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.P ⊓ hyp.base.U = ⊥ := by
  obtain ⟨data, _⟩ := OddOrder.Peterfalvi.S15.basic_structure hG hyp.base
  have : IsMulCommutative ↥hyp.base.P :=
    IsMulCommutative.of_comm data.P_elementaryAbelian.comm
  have hP_le_cent : hyp.base.P ≤ Subgroup.centralizer (hyp.base.P : Set G) :=
    Subgroup.le_centralizer (H := hyp.base.P)
  have hC_bot : hyp.base.C = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [← hyp.base.c_eq_card_C,
      hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply]
  rw [eq_bot_iff, ← hC_bot, hyp.base.C_eq]
  exact le_inf inf_le_right (inf_le_left.trans hP_le_cent)

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Coq `frobPU` (`PFsection14.v:111-124`), realized**: given a (9.7.b) field-model package —
an additive isomorphism `e : Additive ↥P ≃+ 𝔽_{p^q}` with an **injective** character
`μ : U ↪ 𝔽_{p^q}^×` linearizing the conjugation action of `U` on `P` — the derived subgroup
`S' = P ⋊ U` is a **Frobenius group with kernel `P`**.  This is the Lean form of the Coq
derivation `typeP_Galois_P … → Frobenius_semiregularP`: a `U`-element fixing a nonidentity
`P`-point forces `μ(u) = 1`, i.e. `u = 1` — the Frobenius (semiregularity) condition.  The
`u`-**value** `|U| = (p^q−1)/(p−1)` is deliberately *not* an input: (13.15) supplies it only in
the `p ≢ 1 (mod q)` branch (`qu = (p^q−1)/(p−1)` in the other), and Coq's `frobPU` never
consumes it — only the injectivity of the model (issue 0115 statement audit).  The complement
structure is the carrier: `S' = P ⊔ U` (`S_deriv_eq_PU`), `P ⊓ U = ⊥` (`P_inf_U_eq_bot`), `P`
normal in `S` (`maxNilpotentNormalHall`), `P ≠ ⊥` (`P_ne_bot`), and `U ≠ ⊥` from the §13
`U ⋊ W₁` Frobenius structure (`basic_structure`). -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hrepr : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
      ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
        (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
        Function.Injective μ ∧
        ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
              ↥hyp.base.P))
            = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x)) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG hyp.base.S)
      (hyp.base.P.subgroupOf (derivedInG hyp.base.S))
      (hyp.base.U.subgroupOf (derivedInG hyp.base.S)) := by
  classical
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hP_le : hyp.base.P ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU]; exact le_sup_left
  have hU_le : hyp.base.U ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU]; exact le_sup_right
  have hS'_le : derivedInG hyp.base.S ≤ hyp.base.S := Subgroup.map_subtype_le _
  -- `P` is `S`-conjugation-stable (`maxNilpotentNormalHall` is normal in `S`)
  have hPconjS : ∀ s ∈ hyp.base.S, ∀ x ∈ hyp.base.P, s * x * s⁻¹ ∈ hyp.base.P := by
    intro s hs x hx
    have hnrm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.base.S
    have := hnrm.conj_mem ⟨x, hP_le.trans hS'_le hx⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hyp.base.P_eq_SF ▸ hx) ⟨s, hs⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact hyp.base.P_eq_SF ▸ this
  -- normality of `P.subgroupOf S'` in `↥S'` (used twice: the field and the product)
  have hnormal : (hyp.base.P.subgroupOf (derivedInG hyp.base.S)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hPconjS (g : G) (hS'_le g.2) (n : G) hn
  refine
    { isNormal := hnormal
      isComplement := ?_
      ne_bot_kernel := ?_
      ne_bot_complement := ?_
      conj_frobenius := ?_ }
  · -- complement: disjoint + full product
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro z hzP hzU
      rw [Subgroup.mem_subgroupOf] at hzP hzU
      have : (z : G) ∈ hyp.base.P ⊓ hyp.base.U := ⟨hzP, hzU⟩
      rw [P_inf_U_eq_bot hG hyp, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · -- `N ⊔ A = ⊤` (carrier `S' = P ⊔ U`) and `N` normal ⟹ `↑N * ↑A = univ`
      have := hnormal
      have hsup : hyp.base.P.subgroupOf (derivedInG hyp.base.S)
          ⊔ hyp.base.U.subgroupOf (derivedInG hyp.base.S) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hP_le hU_le, ← hyp.base.S_deriv_eq_PU]
        exact Subgroup.subgroupOf_self _
      calc (hyp.base.P.subgroupOf (derivedInG hyp.base.S) : Set ↥(derivedInG hyp.base.S))
            * (hyp.base.U.subgroupOf (derivedInG hyp.base.S) : Set ↥(derivedInG hyp.base.S))
          = ((hyp.base.P.subgroupOf (derivedInG hyp.base.S)
              ⊔ hyp.base.U.subgroupOf (derivedInG hyp.base.S) :
                Subgroup ↥(derivedInG hyp.base.S)) : Set ↥(derivedInG hyp.base.S)) := by
            rw [Subgroup.normal_mul]
        _ = Set.univ := by rw [hsup]; simp
  · -- `P ≠ ⊥`
    intro hbot
    have hPbot : hyp.base.P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hP_le hx⟩ : ↥(derivedInG hyp.base.S))
          ∈ hyp.base.P.subgroupOf (derivedInG hyp.base.S) :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    exact P_ne_bot hG hyp.base hPbot
  · -- `U ≠ ⊥`: the §13 `U ⋊ W₁` Frobenius structure has nontrivial kernel `U`
    intro hbot
    have hUbot : hyp.base.U = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hU_le hx⟩ : ↥(derivedInG hyp.base.S))
          ∈ hyp.base.U.subgroupOf (derivedInG hyp.base.S) :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    obtain ⟨data, -⟩ := OddOrder.Peterfalvi.S15.basic_structure hG hyp.base
    exact data.UW1_frobenius.ne_bot_kernel (by rw [hUbot, Subgroup.bot_subgroupOf])
  · -- semiregularity from the (9.7.b) field model
    intro a haA ha1 n hnN hn1 heq
    rw [Subgroup.mem_subgroupOf] at haA hnN
    obtain ⟨e, μ, hμinj, hcompat⟩ := hrepr
    set v : ↥hyp.base.U := ⟨(a : G), haA⟩
    set x : ↥hyp.base.P := ⟨(n : G), hnN⟩
    have hGeq : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      simpa using congrArg Subtype.val heq
    -- transport the fix through the field model: `e(x) = μ(v)·e(x)`
    have hfix : e (Additive.ofMul x) =
        ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x) := by
      have h := hcompat v x
      rw [show (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ : ↥hyp.base.P) = x from
        Subtype.ext hGeq] at h
      exact h
    -- a field element fixed by a nontrivial unit is zero; injectivity finishes
    have hcases : ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
        GaloisField hyp.base.p hyp.base.q) = 1 ∨ e (Additive.ofMul x) = 0 := by
      have : (((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q) - 1) * e (Additive.ofMul x) = 0 := by
        rw [sub_mul, one_mul, ← hfix, sub_self]
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr h
    rcases hcases with h | h
    · -- `μ(v) = 1 → v = 1 → a = 1`
      apply ha1
      have hv1 : v = 1 := hμinj (by ext : 1; simpa using h)
      exact Subtype.ext (show (a : G) = 1 from congrArg Subtype.val hv1)
    · -- `e(x) = 0 → x = 1 → n = 1`
      apply hn1
      have hx0 : Additive.ofMul x = 0 := e.injective (by rw [map_zero]; exact h)
      have hx1 : x = 1 := Additive.ofMul.injective hx0
      exact Subtype.ext (show (n : G) = 1 from congrArg Subtype.val hx1)

end OddOrder.Peterfalvi.S16
