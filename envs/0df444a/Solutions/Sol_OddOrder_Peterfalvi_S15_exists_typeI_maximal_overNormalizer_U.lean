-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.exists_typeI_maximal_overNormalizer_U
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:01.279106+00:00
-- url     : https://prove2.me/submissions/2bfdfb38-1543-4d3c-b5da-a9e8dc2f2fdf

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean
--   OddOrder/GroupTheory/CoprimeAction.lean
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndTDefs.lean
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SemidirectProduct
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
import Theorems.Thm_OddOrder_GroupTheory_isFrobenius_kernel_eq_bot_of_frobenius_subgroup
import Theorems.Thm_OddOrder_Peterfalvi_S15_card_LF_coprime_pq
import Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_le_of_isHall_subgroupOf_of_conj
import Theorems.Thm_OddOrder_Peterfalvi_S15_exists_conj_typeP_U_of_coprime
import Theorems.Thm_OddOrder_Peterfalvi_S15_coprime_card_U_card_P_of_disjoint
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient

-- ===== OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean =====
namespace OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

variable [Finite G]

/-- **Conjugate subgroups have the same type I status**: if `L` is type I and `conj g • L = M`,
then `M` is type I.  The Peterfalvi (13.17.b) input ruling out conjugacy of a type-`I` subgroup to
the type-II subgroups `S`, `T`. -/
theorem isTypeI_of_conj {L M : Subgroup G} (h : IsTypeI L) {g : G}
    (hconj : MulAut.conj g • L = M) : IsTypeI M :=
  hconj ▸ isTypeI_pointwise_smul (MulAut.conj g) h

end OddOrder.GroupTheory

-- ===== OddOrder/GroupTheory/CoprimeAction.lean =====
namespace OddOrder.GroupTheory

section FrobeniusCentralizer

open OddOrder.Isaacs

variable {L : Type*} [Group L] [Finite L] {N A : Subgroup L}

/-- **A subgroup meeting the Frobenius kernel trivially is coprime to it.**  In a finite Frobenius
group with kernel `N` and complement `A`, if `K ⊓ N = ⊥` then `|K| ⟂ |N|`: `K` injects into the
quotient `L / N`, so `|K| ∣ [L : N] = |A|`, which is prime to `|N|`
(`coprime_card_kernel_complement`).  Reusable; supplies the `coprime_order` of the (9.1) action. -/
theorem IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot
    (h : Ch06.IsFrobeniusGroup L N A) {K : Subgroup L} (hKN : K ⊓ N = ⊥) :
    Nat.Coprime (Nat.card ↥K) (Nat.card ↥N) := by
  have := h.isNormal
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    exact Subtype.ext (Subgroup.disjoint_def.mp (disjoint_iff.mpr hKN) a.2 ha)
  have hdvd : Nat.card ↥K ∣ N.index := by
    rw [Subgroup.index_eq_card]; exact Subgroup.card_dvd_of_injective _ hinj
  rw [h.isComplement.symm.index_eq_card] at hdvd
  exact Nat.Coprime.coprime_dvd_left hdvd h.coprime_card_kernel_complement.symm

/-- The ambient-`G` form of `coprime_card_of_inf_kernel_eq_bot`: for a Frobenius group `Lsub ≤ G`
with kernel `N` (`N ≤ Lsub`), a subgroup `K ≤ Lsub` meeting `N` trivially is coprime to `N`. -/
theorem IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le {G : Type*} [Group G] [Finite G]
    {Lsub N K : Subgroup G} {A : Subgroup ↥Lsub} (hNL : N ≤ Lsub) (hKL : K ≤ Lsub)
    (h : Ch06.IsFrobeniusGroup ↥Lsub (N.subgroupOf Lsub) A) (hKN : K ⊓ N = ⊥) :
    Nat.Coprime (Nat.card ↥K) (Nat.card ↥N) := by
  have hsub : (K.subgroupOf Lsub) ⊓ (N.subgroupOf Lsub) = ⊥ := by
    rw [show K.subgroupOf Lsub ⊓ N.subgroupOf Lsub = (K ⊓ N).subgroupOf Lsub from
      (Subgroup.comap_inf K N Lsub.subtype).symm, hKN, Subgroup.bot_subgroupOf]
  have hcop := IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot h hsub
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv] at hcop

end FrobeniusCentralizer

end OddOrder.GroupTheory

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

-- ===== OddOrder/Peterfalvi/S15_SAndTDefs.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Coherence bridge for Pf (13.17), L~S rule-out**: for `S` of type II, the configuration
complement `U` (coprime to `P = S_F`) has `N_G(U) ⊄ S`.

`U` and the type-data complement `typeP.U` are both `P`-complements in `M' = derivedInG S`
(`P ◁ M'`, solvable), hence conjugate by some `x ∈ M' ≤ S` (Schur–Zassenhaus,
`exists_conj_le_of_isComplement'_of_coprime`).  Transferring the type-II property
`IsTypeII.normalizer_not_le` (`¬ N_G(typeP.U) ≤ S`) along `conj x` (`normalizer_conj_smul`;
`conj x` fixes the subgroup `S` as `x ∈ S`) gives `N_G(U) ⊄ S`.

The `Coprime |U| |P|` hypothesis is the (13.2) faithfulness datum (`U` is the `(κ∪σ)'`-complement,
`p ∈ σ`); it is supplied by the enriched §16 Hypothesis (Phase 0(b),
`notes/peterfalvi/s13_17_structural_program.md`).  The Schur–Zassenhaus conjugacy step itself is
isolated as `exists_conj_typeP_U_of_coprime` below. -/
theorem not_normalizer_U_le_S [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.S)
    (hconj : ∃ x : G, x ∈ hyp.S ∧ hyp.U = MulAut.conj x • tdata.typeP.U) :
    ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S := by
  obtain ⟨x, hxS, hUconj⟩ := hconj
  intro hNUS
  refine tdata.normalizer_not_le ?_
  have hSfix : MulAut.conj x • hyp.S = hyp.S :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hxS)
  have hnorm_eq : Subgroup.normalizer (hyp.U : Set G)
      = MulAut.conj x • Subgroup.normalizer ((tdata.typeP.U : Subgroup G) : Set G) := by
    rw [hUconj]
    exact (OddOrder.BG.Ch3.S12.normalizer_conj_smul x tdata.typeP.U).symm
  rw [hnorm_eq] at hNUS
  have hle : MulAut.conj x • Subgroup.normalizer ((tdata.typeP.U : Subgroup G) : Set G)
      ≤ MulAut.conj x • hyp.S := by rw [hSfix]; exact hNUS
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp hle

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- A subgroup `H ≤ V` whose order is coprime to its index `[V : H]` is a Hall subgroup of `V`
for `π = π(|H|)` (its own set of prime divisors).  The Hall conditions are immediate:
`π(|H|) ⊆ π` by definition, and no prime of `[V : H]` divides `|H|`, by coprimality. -/
theorem isHall_subgroupOf_primeFactors_of_coprime_index [Finite G] {V H : Subgroup G}
    (hHV : H ≤ V) (hcop : Nat.Coprime (Nat.card ↥H) ((H.subgroupOf V).index)) :
    Ch03.IsHallSubgroup {p | p ∈ (Nat.card ↥H).primeFactors} (H.subgroupOf V) := by
  have hcard : Nat.card ↥(H.subgroupOf V) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHV).toEquiv
  refine ⟨fun p hp => by rw [hcard] at hp; exact hp, fun p hp hpπ => ?_⟩
  rw [Nat.mem_primeFactors] at hp
  have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd (Nat.mem_primeFactors.mp hpπ).2.1 hp.2.1
  exact absurd (Nat.dvd_one.mp hp1) hp.1.ne_one

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.17.a) T-side Fitting order (B1)**: `|Q| = |T_F| = q^p`.

This is the `S ↔ T` symmetric companion of `BasicStructureData.P_order` (`|P| = |S_F| = p^q`), now
**proven** for the (14.9) type-II member `T`: from `IsTypeII T`, the (9.3) Wielandt order relation
`typeII_III_IV_order_relations` on the reconciled type-`P` data of `T` (`reconciled_typePData_T`)
gives `|T_F| = |tpd.W2|^|tpd.W1| = |W₁|^|W₂| = q^p` (the intrinsic factors reconcile to
`tpd.W2 = W₁`,
`tpd.W1 = W₂`).  Combined with the automorphism-equivariance of `M_F`
(`maxNilpotentNormalHall_pointwise_smul`), it gives `|L_F| = q^p` for every `L` conjugate to `T`,
which is what the `L ~ T` exclusion of (13.17.a) uses.  The `IsTypeII T` hypothesis is threaded from
`exists_LHypothesis` (§16, via the (14.9) `T_typeII`). -/
theorem card_Q_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  obtain ⟨tpd, _htpdV, htpdW1, htpdW2⟩ := reconciled_typePData_T hG hyp
  have tdata : TypeIIData hyp.T := hTTypeII.some
  have hUne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hW1prime : (Nat.card ↥tpd.W1).Prime := by
    rw [htpdW1, ← hyp.p_eq_card_W2]; exact hyp.p_prime
  have hTI := tdata.common.2.2
  have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
    { maximal := hyp.T_maximal
      typeP := tpd
      nontrivial := ⟨hUne, hW1prime, hTI⟩
      type_alt := Or.inl hTTypeII }).1 hTTypeII
  have hord2 : Nat.card ↥tpd.H = Nat.card ↥tpd.W2 ^ Nat.card ↥tpd.W1 := hord.2
  have hW2card : Nat.card ↥tpd.W2 = hyp.q := by
    rw [htpdW2, ← hyp.q_eq_card_W1]
  rw [tpd.H_eq, ← hyp.Q_eq_TF, hW2card, htpdW1, ← hyp.p_eq_card_W2] at hord2
  exact hord2

/-- **Peterfalvi (13.17.a), `T`-conjugate Fitting order** — the **proven** part (1) of
`tConjugate_fitting_data`: for `L` conjugate to `T` (`conj g • L = T`), `|L_F| = q^p`.

`M_F` is automorphism-equivariant (`maxNilpotentNormalHall_pointwise_smul`), so
`conj g • L_F = maxNilpotentNormalHall (conj g • L) = maxNilpotentNormalHall T = Q`; conjugation
preserves cardinality, so `|L_F| = |Q| = q^p` (`card_Q_eq`, now proven for the (14.9) type-II
`T`). -/
theorem tConjugate_card_LF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    {L : Subgroup G} {g : G} (hconj : MulAut.conj g • L = hyp.T) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.q ^ hyp.p := by
  have hMF : MulAut.conj g • maxNilpotentNormalHall L = hyp.Q := by
    rw [maxNilpotentNormalHall_pointwise_smul, hconj, ← hyp.Q_eq_TF]
  have hcard : Nat.card ↥(maxNilpotentNormalHall L) = Nat.card ↥hyp.Q := by
    rw [← hMF]
    exact Nat.card_congr
      (Subgroup.equivSMul (MulAut.conj g) (maxNilpotentNormalHall L)).toEquiv
  rw [hcard]; exact card_Q_eq hG hyp hTTypeII

/-- **Peterfalvi (13.17.a) T-conjugate Fitting structure**: for a maximal subgroup `L` conjugate
to `T` (`conj g • L = T`), the Fitting kernel `L_F` is a `q`-group of order `q^p` that contains
the cyclic factor `W₁` and meets the complement `U` trivially.

* `|L_F| = q^p` is the transfer of `card_Q_eq` (B1) along `maxNilpotentNormalHall_pointwise_smul`;
* `W₁ ≤ L_F` holds because `W₁ ⊆ N_G(U) ⊆ L` is a `q`-subgroup of `L` and `L_F` is the
  normal `q`-Hall subgroup (Pf p.81 "as `W₁ ⊆ N_G(U) ⊆ L`, `W₁ ⊆ H`");
* `L_F ⊓ U = 1` because `L_F` is a `q`-group while `|U| = u` is prime to `q` (Pf (13.2.a)).

These are exactly the three facts the `L ~ T` branch of (13.17.a) consumes before deriving
`[U, W₁] ⊆ L_F ⊓ U = 1` against the `U W₁` Frobenius structure.  The `card`-equality part is
the isolated §13 residual (`card_Q_eq`); `W₁ ≤ L_F` and `L_F ⊓ U = ⊥` are the §13.2-level
structural data.  **Now proven**: part (1) is `tConjugate_card_LF` (via `card_Q_eq`); part (2)
`W₁ ≤ L_F` places the `q`-group `W₁ ⊆ N_G(U) ⊆ L` in the normal `q`-Hall `L_F`
(`pgroup_le_of_normal_coprime_index`); part (3) `L_F ⊓ U = ⊥` from `|L_F| = q^p` coprime to `|U|`
(the `U ⋊ W₁` Frobenius gives `(|U|, q) = 1`).  `IsTypeII T` is threaded from
`exists_typeI_maximal_overNormalizer_U` (via (14.9) `T_typeII`); `hNUL` is the `N_G(U) ⊆ L`
context. -/
theorem tConjugate_fitting_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    {L : Subgroup G} {g : G} (hconj : MulAut.conj g • L = hyp.T)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.q ^ hyp.p ∧
      hyp.W1 ≤ maxNilpotentNormalHall L ∧
      maxNilpotentNormalHall L ⊓ hyp.U = ⊥ := by
  have hLFcard : Nat.card ↥(maxNilpotentNormalHall L) = hyp.q ^ hyp.p :=
    tConjugate_card_LF hG hyp hTTypeII hconj
  -- `W₁ ⊆ N_G(U) ⊆ L`.
  have hW1leL : hyp.W1 ≤ L := hyp.W1_normalizes_U.trans hNUL
  -- part 2: `W₁ ≤ L_F` — `W₁` is a `q`-group in `L`, `L_F` the normal `q`-Hall subgroup.
  have hW1leLF : hyp.W1 ≤ maxNilpotentNormalHall L := by
    refine pgroup_le_of_normal_coprime_index (S := L) hyp.q_prime hW1leL
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L) ?_ ?_ ?_
    · have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall L
      have hcard_eq : Nat.card ↥((maxNilpotentNormalHall L).subgroupOf L)
          = Nat.card ↥(maxNilpotentNormalHall L) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L)).toEquiv
      exact hcard_eq ▸ Ch03.IsHallSubgroup.coprime_index hHall
    · rw [hLFcard]; exact dvd_pow_self hyp.q hyp.p_prime.pos.ne'
    · intro w hw
      have heq : orderOf (⟨w, hw⟩ : ↥hyp.W1) = orderOf w :=
        (orderOf_injective hyp.W1.subtype Subtype.coe_injective ⟨w, hw⟩).symm
      have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W1) ∣ Nat.card ↥hyp.W1 := orderOf_dvd_natCard _
      rw [heq, ← hyp.q_eq_card_W1] at h1
      exact h1
  -- part 3: `L_F ⊓ U = ⊥` — `L_F` a `q`-group (`|L_F| = q^p`), `U` coprime to `q` (`U ⋊ W₁`
  -- Frobenius).
  have hLFU : maxNilpotentNormalHall L ⊓ hyp.U = ⊥ := by
    obtain ⟨data, _⟩ := basic_structure hG hyp
    have hcopUq : Nat.Coprime (Nat.card ↥hyp.U) hyp.q := by
      have hk := data.UW1_frobenius.coprime_card_kernel_complement
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
        ← hyp.q_eq_card_W1] at hk
      exact hk
    have hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (Nat.card ↥hyp.U) := by
      rw [hLFcard]; exact hcopUq.symm.pow_left hyp.p
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  exact ⟨hLFcard, hW1leLF, hLFU⟩

/-- **Frobenius-kernel self-centralizing (the gate-4 final step)**: in a finite Frobenius group `L`
with kernel `N`, any abelian subgroup `U` meeting `N` nontrivially lies in `N`.  Picking
`1 ≠ x ∈ U ⊓ N`, every `u ∈ U` commutes with `x` (`U` abelian), so `u ∈ C_L(x) ≤ N`
(`IsFrobeniusGroup.centralizer_kernel_le`: the centralizer of a nontrivial kernel element lies in
the kernel).  This is exactly the `U ⊆ C_L(U ∩ L_F) ⊆ L_F` deduction of Peterfalvi (13.17.b) once
`U ∩ L_F ≠ 1` is known.  General group theory; reusable, hoistable to `Ch06`. -/
theorem le_kernel_of_isMulCommutative_of_inf_ne_bot {L : Type*} [Group L] [Finite L]
    {N A U : Subgroup L} (h : Ch06.IsFrobeniusGroup L N A)
    (hUab : IsMulCommutative ↥U) (hinf : U ⊓ N ≠ ⊥) : U ≤ N := by
  obtain ⟨x, hxmem, hxne⟩ := (U ⊓ N).bot_or_exists_ne_one.resolve_left hinf
  have hxU : x ∈ U := (Subgroup.mem_inf.mp hxmem).1
  have hxN : x ∈ N := (Subgroup.mem_inf.mp hxmem).2
  have hcent := h.centralizer_kernel_le x hxN hxne
  intro u hu
  refine hcent (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  exact congrArg Subtype.val (hUab.is_comm.comm ⟨u, hu⟩ ⟨x, hxU⟩)

/-- **Type is conjugacy-invariant** (the (13.17.a/b) `L ~ S`/`L ~ T` rule-out): a type-`I` maximal
subgroup `L` is not conjugate to any non-type-`I` maximal subgroup `M`.  If `conj g • L = M` then
`M` would be type `I` (`isTypeI_of_conj`, the automorphism-equivariance of the Peterfalvi taxonomy
— `OddOrder.GroupTheory.MaximalSubgroupTypeConj`), contradicting
`not_isTypeI_of_isTypeNonI`.  This is **gate-4 piece 1**, now discharged (sorry-free, axiom-clean);
reusable across the §16 conjugacy arguments. -/
theorem not_conj_of_isTypeI_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L M : Subgroup G} (hLI : IsTypeI L) (hMmax : M ∈ maximalSubgroups G)
    (hMnonI : IsTypeNonI M) : ¬ ∃ g : G, MulAut.conj g • L = M :=
  fun ⟨_g, hg⟩ =>
    OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG hMmax hMnonI
      (OddOrder.GroupTheory.isTypeI_of_conj hLI hg)

/-- **Peterfalvi (13.17.b), the (9.1) fixed-point-free residual (gate-4 pieces 4–6)**: once the
(8.17.a) coprimality `|L_F| ⟂ p q` is in hand for the type-`I` `L` over `N_G(U)`, the complement
`U` lies in the Fitting kernel `L_F`.  As `|W₁| = q ∤ |L_F|`, `W₁ ∩ L_F = 1`; were `U ∩ L_F = 1`,
the Frobenius group `U W₁ ⊆ L` (from (13.2.a)) would act fixed-point-freely on `L_F`
(`U, W₁ ≤ L ≤ N_G(L_F)`, a coprime action), so Wielandt's formula (9.1)
`wielandt_fixedPoint_frobenius` would force `|L_F| = 1`, against type-`I` `L_F ≠ 1`
(`TypeFData.H_nontrivial`); hence `U ∩ L_F ≠ 1` and `U ⊆ C_L(U ∩ L_F) ⊆ L_F`
(`le_kernel_of_isMulCommutative_of_inf_ne_bot`).  The deep part of gate 4 is the
`CoprimeFrobeniusAction (U W₁) (L_F)` construction together with the Wielandt formula; both are
proved.  See issue 2009 / `notes/peterfalvi/s13_17_structural_program.md`. -/
theorem typeI_U_le_fitting_of_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (_hSTypeII : IsTypeII hyp.S) {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (hyp.p * hyp.q)) :
    hyp.U ≤ maxNilpotentNormalHall L := by
  -- The (12.7) Frobenius structure of the type-`I` `L`, with kernel
  -- `L_F = maxNilpotentNormalHall L`.
  obtain ⟨frob, _⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV hLmax hLI
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hfrobLF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((maxNilpotentNormalHall L).subgroupOf L) frob.complement := hHeq ▸ frob.frobenius
  have hUleL : hyp.U ≤ L := Subgroup.le_normalizer.trans hNUL
  have hW1leL : hyp.W1 ≤ L := hyp.W1_normalizes_U.trans hNUL
  have hLFleL : maxNilpotentNormalHall L ≤ L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  obtain ⟨bdata, _⟩ := basic_structure hG hyp
  have hsolv : Group.IsSolvable ↥(maxNilpotentNormalHall L) := by
    have := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
    exact IsNilpotent.to_isSolvable
  -- piece 3: `W₁ ⊓ L_F = ⊥`, since `q = |W₁|` divides `p q` and `|L_F| ⟂ p q`.
  have hcopLFq : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.q :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left hyp.q hyp.p) hcop
  have hW1LF : hyp.W1 ⊓ maxNilpotentNormalHall L = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [← hyp.q_eq_card_W1]; exact hcopLFq.symm)).eq_bot
  -- piece 5: `U ⊓ L_F ≠ ⊥` (else the Frobenius `U W₁` acts fixed-point-freely on `L_F`).
  have hUmeets : hyp.U ⊓ maxNilpotentNormalHall L ≠ ⊥ := by
    intro hbot
    have hcopU : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hUleL hfrobLF hbot
    have hcopW1 : Nat.Coprime (Nat.card ↥hyp.W1) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hW1leL hfrobLF hW1LF
    have hcardUW1 : Nat.card ↥(hyp.U ⊔ hyp.W1) = Nat.card ↥hyp.U * Nat.card ↥hyp.W1 := by
      rw [← bdata.UW1_frobenius.isComplement.card_mul_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    have hcopUW1 : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L))
        (Nat.card ↥(hyp.U ⊔ hyp.W1)) := by
      rw [hcardUW1]; exact Nat.Coprime.mul_right hcopU.symm hcopW1.symm
    have hLFbot : maxNilpotentNormalHall L = ⊥ :=
      OddOrder.GroupTheory.isFrobenius_kernel_eq_bot_of_frobenius_subgroup hLFleL
        (sup_le hUleL hW1leL) ⟨frob.complement, hfrobLF⟩ bdata.UW1_frobenius hbot hW1LF hsolv
          hcopUW1
    exact frob.frobenius.ne_bot_kernel (by rw [hHeq, hLFbot, Subgroup.bot_subgroupOf])
  -- piece 6: `U ⊆ C_L(U ∩ L_F) ⊆ L_F` since `U` is abelian and `L_F` is the Frobenius kernel.
  have hUab : IsMulCommutative ↥(hyp.U.subgroupOf L) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hUleL).symm hyp.S_U_commutative
  have hinf : (hyp.U.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L) ≠ ⊥ := by
    rw [show (hyp.U.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L)
        = (hyp.U ⊓ maxNilpotentNormalHall L).subgroupOf L from (Subgroup.comap_inf _ _ _).symm]
    intro h
    apply hUmeets
    have hle : hyp.U ⊓ maxNilpotentNormalHall L ≤ L := inf_le_right.trans hLFleL
    rw [← inf_eq_left.mpr hle]
    exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
  have hsub := le_kernel_of_isMulCommutative_of_inf_ne_bot hfrobLF hUab hinf
  calc hyp.U = (hyp.U.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hUleL).symm
    _ ≤ ((maxNilpotentNormalHall L).subgroupOf L).map L.subtype := Subgroup.map_mono hsub
    _ = maxNilpotentNormalHall L := Subgroup.map_subgroupOf_eq_of_le hLFleL

/-- **Peterfalvi (13.17.b) `U ⊆ L_F` for the type-`I` `L`**: when `S` is type II and `L` is a
type-`I` maximal subgroup over `N_G(U)`, the complement `U` lies in the Fitting kernel `L_F`.

*Proof (Pf p.82, the gate-4 structural core):* `L` is non-conjugate to `S` and `T` (it is type `I`
while `S`, `T` are non-I and type is conjugacy-invariant — `not_conj_of_isTypeI_of_isTypeNonI`, the
**discharged gate-4 piece 1**), so (8.17.a) = `card_LF_coprime_pq` (B2) gives `|L_F|` prime to
`p q`, in particular to `q = |W₁|`.  The remaining (9.1) fixed-point-free argument
(`W₁ ∩ L_F = 1`; `U ∩ L_F ≠ 1` by Wielandt; `U ⊆ C_L(U ∩ L_F) ⊆ L_F`) is
`typeI_U_le_fitting_of_coprime` (the isolated deep residual of gate 4).

Assembled `sorry`-free from the piece-1 non-conjugacy, the (8.17.a) coprimality producer
`card_LF_coprime_pq` (owner = F, BG Theorem E), and `typeI_U_le_fitting_of_coprime`. -/
theorem typeI_overNormalizer_U_le_fitting [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (_hSTypeII : IsTypeII hyp.S) {L : Subgroup G} (_hLmax : L ∈ maximalSubgroups G)
    (_hLI : IsTypeI L) (_hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    hyp.U ≤ maxNilpotentNormalHall L := by
  -- (piece 1) `L` is non-conjugate to `S`, `T` (type is conjugacy-invariant; `S`, `T` are non-I).
  have hnS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG _hLI hyp.S_maximal hyp.S_nonI
  have hnT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG _hLI hyp.T_maximal hyp.T_nonI
  -- (piece 2) the (8.17.a) coprimality, then (pieces 4–6) the isolated FPF residual.
  exact typeI_U_le_fitting_of_coprime _hG hnoV hyp _hSTypeII _hLmax _hLI _hNUL
    (card_LF_coprime_pq _hG hyp _hLmax _hLI hnS hnT)

/-- **Peterfalvi (13.17.a/b)**: a maximal subgroup `L` over `N_G(U)` (for `S` of type II) is of
type I with `U ⊆ L_F`.  *Proof (Pf pp.81-82):* take any maximal `L ⊇ N_G(U)` (proper since
`U ≠ 1` and `G` is simple).  `L` is not conjugate to `S` (else `N_G(U) ⊆ S`, against
`IsTypeII.normalizer_not_le`) nor to `T` (else `|L_F| = q^p` forces `[U,W₁] ⊆ L_F ∩ U = 1`,
against `U W₁` Frobenius from (13.2.a)), so by (8.8.b4) `L` is type I.  Then `U ⊆ L_F`: (8.17.a)
gives `|L_F|` prime to `q`, so `W₁ ∩ L_F = 1`; were `U ∩ L_F = 1`, `U W₁` would act
fixed-point-freely on `L_F`, forcing `L_F = 1` by (9.1).  The genuine §13 structural obligation
feeding (13.17); see issue 2009.

*Status:* fully proved and axiom-clean.  The assembly is `U ≠ ⊥` (issue 7008: `U` is
`S`-conjugate to `tdata.typeP.U`, nontrivial by `TypePNontrivialCore`), `N_G(U) ≠ ⊤`
(simplicity), the maximal `L ⊇ N_G(U)`, and the (8.8.b4) trichotomy dispatch, with the type-II
property `N_G(U) ⊄ S` wired in through `not_normalizer_U_le_S ∘ exists_conj_typeP_U_of_coprime ∘
coprime_card_U_card_P_of_disjoint`.  The four former gates are all discharged: `hdisj`
(`P ⊓ U = ⊥`) from the §16 carrier `hyp.Sdata.derived_complement`; the L~S Hall-conjugacy
derivation of `N_G(U) ⊆ S`; the L~T `|L_F| = q^p` exclusion (`tConjugate_fitting_data`); and
`U ⊆ L_F` ((8.17.a)+(9.1)). -/
theorem _root_.solution [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) (hTTypeII : IsTypeII hyp.T) :
    ∃ L : Subgroup G, L ∈ maximalSubgroups G ∧ IsTypeI L ∧
      Subgroup.normalizer (hyp.U : Set G) ≤ L ∧ hyp.U ≤ maxNilpotentNormalHall L := by
  obtain ⟨tdata⟩ := hSTypeII
  -- The configuration complement meets the Fitting kernel trivially.  Now discharged from the
  -- §16 carrier `hyp.Sdata` (the type-`P` data of `S`, reconciled `Sdata.U = U`, `Sdata.H = P`):
  -- `U` complements `M_F = P` in `M' = [S,S]` (`Sdata.derived_complement`), so `P ⊓ U = ⊥`.
  have hdisj : hyp.P ⊓ hyp.U = ⊥ := by
    have key : hyp.Sdata.H ⊓ hyp.Sdata.U = ⊥ := by
      have hd := disjoint_iff.mp hyp.Sdata.derived_complement.disjoint
      rw [eq_bot_iff]
      rintro x ⟨hxH, hxU⟩
      have hxD : x ∈ derivedInG hyp.S := hyp.Sdata.H_le hxH
      have hmem : (⟨x, hxD⟩ : ↥(derivedInG hyp.S)) ∈
          (hyp.Sdata.H.subgroupOf (derivedInG hyp.S)) ⊓
            (hyp.Sdata.U.subgroupOf (derivedInG hyp.S)) :=
        ⟨Subgroup.mem_subgroupOf.mpr hxH, Subgroup.mem_subgroupOf.mpr hxU⟩
      rw [hd, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      simpa using Subtype.ext_iff.mp hmem
    rw [hyp.P_eq_SF, ← hyp.Sdata.H_eq, ← hyp.Sdata_U_eq]
    exact key
  have hcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P) :=
    coprime_card_U_card_P_of_disjoint hyp tdata hdisj
  -- (Phase 1) the type-II property transferred to `hyp.U`: `N_G(U) ⊄ S`.
  have hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S :=
    not_normalizer_U_le_S _hG hyp tdata (exists_conj_typeP_U_of_coprime _hG hyp tdata hcop)
  -- `U ≠ ⊥` (issue 7008): `U` is `S`-conjugate to `tdata.typeP.U`, which is `≠ ⊥` for type II
  -- (the `TypePNontrivialCore` first conjunct `common.1`); conjugation preserves nontriviality.
  have hUne : hyp.U ≠ ⊥ := by
    obtain ⟨x, _, hUconj⟩ := exists_conj_typeP_U_of_coprime _hG hyp tdata hcop
    rw [hUconj]
    exact mt (pointwise_smul_eq_bot_iff (MulAut.conj x)).mp tdata.common.1
  -- `U ≤ S`, hence `U ≠ ⊤`; then by simplicity `N_G(U) ≠ ⊤`.
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hUleS : hyp.U ≤ hyp.S := (le_sup_right.trans hyp.S_deriv_eq_PU.ge).trans hM'_le_S
  have hUneTop : hyp.U ≠ ⊤ := fun hUtop =>
    (mem_maximalSubgroups.mp hyp.S_maximal).1 (top_le_iff.mp (hUtop ▸ hUleS))
  have hNUtop : Subgroup.normalizer (hyp.U : Set G) ≠ ⊤ := by
    intro hNtop
    have hUnormal : (hyp.U).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases _hG.simple.eq_bot_or_eq_top_of_normal hyp.U hUnormal with h | h
    · exact hUne h
    · exact hUneTop h
  -- a maximal subgroup `L ⊇ N_G(U)`.
  obtain ⟨L, hNUL, hLmaximal⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G => K ≠ ⊤) hNUtop
  have hLmem : L ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr ⟨hLmaximal.1, fun b hLb => by
      by_contra hbne
      exact lt_irrefl L (lt_of_lt_of_le hLb (hLmaximal.2 hbne hLb.le))⟩
  -- (8.8.b4) trichotomy: `L` is type I, or conjugate to `S`, or conjugate to `T`.
  rcases hyp.theorem88_caseB L hLmem with hLI | _hLconjS | _hLconjT
  · -- `L` is type I; conclude with `U ⊆ L_F` (Pf (13.17.b)).  The (8.17.a)+(9.1)
    -- FPF structural core — `q ∤ |L_F|` (`card_LF_coprime_pq`), so `W₁ ∩ L_F = 1`;
    -- if `U ∩ L_F = 1` then `U W₁` acts FPF on `L_F`, forcing `L_F = 1` by
    -- `wielandt_fixedPoint_frobenius`, against type-`I` `L_F ≠ 1`; hence `U ∩ L_F ≠ 1` and
    -- `U ⊆ C_L(U ∩ L_F) ⊆ L_F` — is `typeI_overNormalizer_U_le_fitting`.
    exact ⟨L, hLmem, hLI, hNUL,
      typeI_overNormalizer_U_le_fitting _hG hnoV hyp ⟨tdata⟩ hLmem hLI hNUL⟩
  · -- `L` conjugate to `S` is excluded (`_hLconjS`): Pf (13.17.a) derives `N_G(U) ⊆ S` from the
    -- Hall conjugacy of `U` in the solvable `S`, contradicting `hNUS`.  The structural argument is
    -- `normalizer_le_of_isHall_subgroupOf_of_conj`; its only `S`-specific input is "`U` is a Hall
    -- subgroup of `S`".  That coprimality `|U| ⟂ [S:U]` is the residual (13.2) Hall-faithfulness
    -- datum: `[S:U] = [S:M']·|P|`, `|U| ⟂ |P|` is `hcop`, and `|U| ⟂ [S:M']` holds because
    -- `[S:M'] = |W₁|` is the order of the cyclic κ(S)-Hall complement of `M'` (Pf's `W₁`),
    -- coprime to `|M'| ⊇ |U|`.  The `W₁ = κ(S)`-Hall identification is the carrier-level fact
    -- supplied at the §16 `Section16MaximalPair` (lane-f) but not pinned by the bare `Hypothesis`;
    -- see issue 2009 / `notes/peterfalvi/s13_17_structural_program.md`.
    obtain ⟨g, hg⟩ := _hLconjS
    -- `[S : U] = |P| · |W₁|` from the carrier complements (`U` complements `P` in `M'`,
    -- `W₁` complements `M'` in `S`); coprimality is `|U| ⟂ |P|` (`hcop`) and `|U| ⟂ |W₁|` (the
    -- Frobenius group `U ⋊ W₁` of (13.2.a), `coprime_card_kernel_complement`).
    have hUhall_cop : Nat.Coprime (Nat.card ↥hyp.U) ((hyp.U.subgroupOf hyp.S).index) := by
      obtain ⟨bdata, _⟩ := basic_structure _hG hyp
      have frobcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.W1) := by
        have h := bdata.UW1_frobenius.coprime_card_kernel_complement
        rwa [Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_left : hyp.U ≤ hyp.U ⊔ hyp.W1)).toEquiv,
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_right : hyp.W1 ≤ hyp.U ⊔ hyp.W1)).toEquiv] at h
      have hPleM' : hyp.P ≤ derivedInG hyp.S := le_sup_left.trans hyp.S_deriv_eq_PU.ge
      have hidxM' : ((derivedInG hyp.S).subgroupOf hyp.S).index = Nat.card ↥hyp.W1 := by
        rw [← hyp.Sdata_W1_eq, ← hyp.Sdata.card_W1_eq_derived_index]
      have hidxP : (hyp.P.subgroupOf (derivedInG hyp.S)).index = Nat.card ↥hyp.U := by
        rw [hyp.P_eq_SF, ← hyp.Sdata.card_U_eq_index, hyp.Sdata_U_eq]
      have hScard : Nat.card ↥hyp.S
          = Nat.card ↥hyp.W1 * (Nat.card ↥hyp.U * Nat.card ↥hyp.P) := by
        have e1 := ((derivedInG hyp.S).subgroupOf hyp.S).index_mul_card
        have e2 := (hyp.P.subgroupOf (derivedInG hyp.S)).index_mul_card
        rw [hidxM', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'_le_S).toEquiv] at e1
        rw [hidxP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleM').toEquiv] at e2
        rw [← e1, ← e2]
      have hidxU := (hyp.U.subgroupOf hyp.S).index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleS).toEquiv] at hidxU
      have hidxUeq : (hyp.U.subgroupOf hyp.S).index = Nat.card ↥hyp.P * Nat.card ↥hyp.W1 := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥hyp.U))
        rw [hidxU, hScard]; ring
      rw [hidxUeq]
      exact hcop.mul_right frobcop
    exact absurd (normalizer_le_of_isHall_subgroupOf_of_conj
        (_hG.isSolvable_of_mem_maximalSubgroups hyp.S_maximal) hUleS
        (isHall_subgroupOf_primeFactors_of_coprime_index hUleS hUhall_cop) hg hNUL) hNUS
  · -- `L` conjugate to `T` is excluded (`_hLconjT`): `|L_F| = q^p` forces `W₁ ⊆ L_F` and
    -- `[U,W₁] ⊆ L_F ∩ U = 1`, contradicting the `U W₁` Frobenius structure (13.2.a).
    exfalso
    obtain ⟨g, hg⟩ := _hLconjT
    -- (B1, `tConjugate_fitting_data`) the T-side Fitting structure of `L_F`:
    -- `|L_F| = q^p`, `W₁ ≤ L_F`, and `L_F ⊓ U = 1`.
    obtain ⟨_hLFcard, hW1le, hLFU⟩ := tConjugate_fitting_data _hG hyp hTTypeII hg hNUL
    -- `U ⊆ L`, hence `U` normalizes `L_F = maxNilpotentNormalHall L`.
    have hUleL : hyp.U ≤ L := Subgroup.le_normalizer.trans hNUL
    have hU_norm_LF : hyp.U ≤ Subgroup.normalizer (maxNilpotentNormalHall L) :=
      hUleL.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L)
    -- `⁅U, W₁⁆ ≤ U` since `W₁` normalizes `U` (`W1_normalizes_U`).
    have hUW1_le_U : ⁅hyp.U, hyp.W1⁆ ≤ hyp.U :=
      OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hyp.W1_normalizes_U
    -- `⁅U, W₁⁆ ≤ ⁅U, L_F⁆ ≤ L_F` since `W₁ ≤ L_F` and `U` normalizes `L_F`.
    have hUW1_le_LF : ⁅hyp.U, hyp.W1⁆ ≤ maxNilpotentNormalHall L := by
      refine (Subgroup.commutator_mono (le_refl hyp.U) hW1le).trans ?_
      rw [Subgroup.commutator_comm]
      exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hU_norm_LF
    -- `⁅U, W₁⁆ ≤ L_F ⊓ U = 1`, so `U` and `W₁` commute elementwise.
    have hUW1_bot : ⁅hyp.U, hyp.W1⁆ = ⊥ :=
      le_bot_iff.mp ((le_inf hUW1_le_LF hUW1_le_U).trans hLFU.le)
    have hUcent : hyp.U ≤ Subgroup.centralizer (hyp.W1 : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUW1_bot
    -- `W₁ ≠ ⊥` (order `q ≥ 2`) and `U ≠ ⊥`: extract nontrivial witnesses contradicting Frobenius.
    have hW1ne : hyp.W1 ≠ ⊥ := by
      intro hbot
      have : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hbot, Subgroup.card_bot]
      exact hyp.q_prime.one_lt.ne' this
    obtain ⟨w, hwW1, hwne⟩ := (hyp.W1.bot_or_exists_ne_one).resolve_left hW1ne
    obtain ⟨n, hnU, hnne⟩ := (hyp.U.bot_or_exists_ne_one).resolve_left hUne
    -- `w * n * w⁻¹ = n` from the commuting (centralizer) relation.
    have hcomm : w * n * w⁻¹ = n := by
      have := hUcent hnU w hwW1
      -- `this : w * n = n * w`; rearrange to `w * n * w⁻¹ = n`.
      rw [mul_inv_eq_iff_eq_mul, this]
    -- Move to the Frobenius group `↥(U ⊔ W₁)` and contradict `conj_frobenius`.
    obtain ⟨bdata, _⟩ := basic_structure _hG hyp
    have hwUW1 : w ∈ hyp.U ⊔ hyp.W1 := Subgroup.mem_sup_right hwW1
    have hnUW1 : n ∈ hyp.U ⊔ hyp.W1 := Subgroup.mem_sup_left hnU
    have hwmem : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1) := hwW1
    have hnmem : (⟨n, hnUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.U.subgroupOf (hyp.U ⊔ hyp.W1) := hnU
    have hwne' : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hwne (congrArg Subtype.val h)
    have hnne' : (⟨n, hnUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hnne (congrArg Subtype.val h)
    have hconj_eq : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) * ⟨n, hnUW1⟩ * ⟨w, hwUW1⟩⁻¹ = ⟨n, hnUW1⟩ :=
      Subtype.ext (by simpa using hcomm)
    exact bdata.UW1_frobenius.conj_frobenius _ hwmem hwne' _ hnmem hnne' hconj_eq

end OddOrder.Peterfalvi.S15
