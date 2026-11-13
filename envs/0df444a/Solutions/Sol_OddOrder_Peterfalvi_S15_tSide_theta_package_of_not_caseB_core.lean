-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.tSide_theta_package_of_not_caseB_core
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:08:40.681184+00:00
-- url     : https://prove2.me/submissions/510ee1b3-ec39-45f5-a145-4859afc769f5

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean
--   OddOrder/Peterfalvi/S15_Tau1T.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean
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
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_thetaWitness_of_caseB_member
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_thetaWitness_of_caseA
import Theorems.Thm_OddOrder_Peterfalvi_S15_P_conj_forall_not_le_T
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S15_inner_eq_zero_of_conj_diff_orthogonal
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_tau1T_ofHonest_nuRow_eta_row
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_K_mem_zSpan_T
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_K_mem_zSpan_sSet_irr_T

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

/-- **Peterfalvi (13.4), conjugate-disjointness core** (abstract form, issue 9013 追記⁶ core (d)):
if every point of `A_M ⊆ M` is centralized by `R`, every point of `A_N ⊆ N` has its centralizer
inside `N` (the TI-shape), and no conjugate of `R` fits inside `N`, then no element of `G` is
simultaneously conjugate into `A_M` and into `A_N`.

In (13.4): `M = S`, `A_M = H^#` with `R = P` (`P_le_centralizer_of_mem_H`); `N = T`,
`A_N = K^# ⊆ A₀(T)` (the (13.2.e) TI-property for `T` bounds the centralizers); and `P^w ≤ T` is
impossible since `|P| = p^q` exceeds the `p`-part `p` of `|T|` — the latter two are the T-side
gates of the (13.4) reduction. -/
theorem disjoint_conjugatesIntoSet_of_centralizer {M N R : Subgroup G}
    {A_M : Set ↥M} {A_N : Set ↥N}
    (hcent : ∀ y ∈ A_M, R ≤ Subgroup.centralizer ({((y : ↥M) : G)} : Set G))
    (hTI : ∀ z ∈ A_N, Subgroup.centralizer ({((z : ↥N) : G)} : Set G) ≤ N)
    (hnot : ∀ w : G, ¬ ∀ r ∈ R, w⁻¹ * r * w ∈ N) :
    Disjoint (ClassFunction.conjugatesIntoSet M A_M)
      (ClassFunction.conjugatesIntoSet N A_N) := by
  rw [Set.disjoint_left]
  rintro g ⟨a, ha, hyA⟩ ⟨b, hb, hzA⟩
  -- The `A_M`-point is `a⁻¹ g a`, the `A_N`-point is `b⁻¹ g b = w⁻¹ (a⁻¹ g a) w` for `w = a⁻¹ b`.
  -- Every `R`-conjugate `w⁻¹ r w` centralizes it, hence lies in `N` — contradicting `hnot`.
  refine hnot (a⁻¹ * b) fun r hr => ?_
  have hrx : (a⁻¹ * g * a) * r = r * (a⁻¹ * g * a) := by
    have h := hcent _ hyA hr
    rw [Subgroup.mem_centralizer_iff] at h
    exact h (a⁻¹ * g * a) rfl
  refine hTI _ hzA ?_
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hs' : s = b⁻¹ * g * b := hs
  rw [hs']
  calc (b⁻¹ * g * b) * ((a⁻¹ * b)⁻¹ * r * (a⁻¹ * b))
      = (a⁻¹ * b)⁻¹ * ((a⁻¹ * g * a) * r) * (a⁻¹ * b) := by group
    _ = (a⁻¹ * b)⁻¹ * (r * (a⁻¹ * g * a)) * (a⁻¹ * b) := by rw [hrx]
    _ = ((a⁻¹ * b)⁻¹ * r * (a⁻¹ * b)) * (b⁻¹ * g * b) := by group

open scoped FiniteInduce in
/-- **Cross-Dade inner-product vanishing on disjoint conjugate supports** ((13.4) core (d)):
the inductions of `α` (supported in `A_M ⊆ M`) and `β` (supported in `A_N ⊆ N`) to `G` have
disjoint supports when nothing is conjugate into both `A_M` and `A_N`, so their inner product
vanishes.  This is Peterfalvi's `(α^τ, β^τ) = 0` for `α ∈ ℤ[𝒮, H^#]`, `β ∈ ℤ[𝒯, K^#]` (both Dade
isometries being `Ind` by (13.2.e), the supports lie in `(H^#)^G` resp. `(K^#)^G`). -/
theorem inner_induce_induce_eq_zero_of_disjoint [Fintype G] [Invertible (Nat.card G : ℂ)]
    {M N : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card ↥N : ℂ)]
    {A_M : Set ↥M} {A_N : Set ↥N}
    {α : ClassFunction ↥M ℂ} {β : ClassFunction ↥N ℂ}
    (hα : α.support ⊆ A_M) (hβ : β.support ⊆ A_N)
    (hdisj : Disjoint (ClassFunction.conjugatesIntoSet M A_M)
      (ClassFunction.conjugatesIntoSet N A_N)) :
    ClassFunction.inner (ClassFunction.induce M α) (ClassFunction.induce N β) = 0 :=
  ClassFunction.inner_eq_zero_of_disjoint_support
    (hdisj.mono (ClassFunction.support_induce_subset_conjugatesIntoSet hα)
      (ClassFunction.support_induce_subset_conjugatesIntoSet hβ))

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

/-- **`P` centralizes every element of `H = PC`** (Peterfalvi (13.4), disjointness ingredient):
for `x ∈ H`, `P ≤ C_G(x)`.  Immediate from `H` abelian (`H_mulCommutative`) and `P ≤ H`.  This is
the first half of the (13.4) conjugate-disjointness `(H^#)^G ∩ (K^#)^G = ∅`: a common point `x`
would have `P ≤ C_G(x) ≤ T^g` (the `A₀(T^g)` TI-property), impossible since `|P| = p^q` exceeds
the `p`-part `p` of `|T|`. -/
theorem Hypothesis.P_le_centralizer_of_mem_H [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {x : G} (hx : x ∈ hyp.H) :
    hyp.P ≤ Subgroup.centralizer ({x} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  have hyH : y ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.P ⊔ hyp.C) hy
  have hcomm := (hyp.H_mulCommutative hG).is_comm.comm (⟨x, hx⟩ : ↥hyp.H) ⟨y, hyH⟩
  simpa using congrArg Subtype.val hcomm

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

/-- **`(QD)^# ⊆ A(T)` membership** ((13.2.e) structural input, issue 0116 step 4): every
nonidentity element of `K = QD` lies in the honest type-`P` support `A(T)`.  Split `z = q·d`
along the `T`-normalized `Q` (`exists_mul_of_mem_sup_of_normalized`); `d ∈ D = C_V(Q)`
centralizes `Q` (`D_eq`), so for `q ≠ 1` the pair `(q, z)` witnesses `z ∈ C_{T'}(q)^#` with
`q ∈ Q^# ⊆ T_σ^#` (`maxNilpotentNormalHall_le_Msigma`), while for `q = 1` (so `z = d ∈ D^#`)
any `x ∈ Q^#` (`Q_ne_bot`) serves as the `T_σ^#`-witness. -/
theorem Hypothesis.mem_typePACore_of_mem_Q_sup_D [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {z : G} (hz : z ∈ hyp.Q ⊔ hyp.D) (hz1 : z ≠ 1) :
    z ∈ S10.typePACore hyp.T := by
  have hQT' : hyp.Q ≤ derivedInG hyp.T := hyp.T_deriv_eq_QV ▸ le_sup_left
  have hDV : hyp.D ≤ hyp.V := hyp.D_eq ▸ inf_le_left
  have hVT' : hyp.V ≤ derivedInG hyp.T := hyp.T_deriv_eq_QV ▸ le_sup_right
  have hQT : hyp.Q ≤ hyp.T := hQT'.trans (Subgroup.map_subtype_le _)
  have hDT : hyp.D ≤ hyp.T := (hDV.trans hVT').trans (Subgroup.map_subtype_le _)
  have hTnorm : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hzT' : z ∈ derivedInG hyp.T := (sup_le hQT' (hDV.trans hVT')) hz
  have hQMs : hyp.Q ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.T_maximal
  obtain ⟨q, hq, d, hd, rfl⟩ :=
    OddOrder.Peterfalvi.S13.exists_mul_of_mem_sup_of_normalized hQT hDT hTnorm hz
  have hdC : d ∈ Subgroup.centralizer (hyp.Q : Set G) :=
    (Subgroup.mem_inf.mp (hyp.D_eq ▸ hd)).2
  by_cases hq1 : q = 1
  · -- `z = d ∈ D^#`: any `x ∈ Q^#` is the `T_σ^#`-witness (`D` centralizes all of `Q`)
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hyp.Q_ne_bot
    refine S10.mem_typePACore.mpr ⟨hzT', hz1, (x : G),
      ⟨hQMs x.2, fun h => hx1 (Subtype.ext h)⟩, ?_⟩
    rw [hq1, one_mul]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x.2) hdC
  · -- `q ≠ 1`: `q` itself is the witness — `q` and `d` both centralize `q`
    refine S10.mem_typePACore.mpr ⟨hzT', hz1, q, ⟨hQMs hq, hq1⟩, ?_⟩
    exact Subgroup.mul_mem _
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hq) hdC)

/-- **(13.2.e)-for-`T`, `K^# = (QD)^#` TI-centralizer gate** ((13.4) structural gate, issue 9013
追記⁶ (c)): every nonidentity element of `K = QD` has its `G`-centralizer inside `T`.
Discharged through the honest `A(T)`-support (issue 0116 step 4): `(QD)^# ⊆ A(T)`
(`mem_typePACore_of_mem_Q_sup_D`), and no `A(T)`-point escapes a type-`P` maximal
(`escaping_typePACore_eq_empty`, the proven (13.2.e) core via BG Theorem D(4)); the
type-V exclusion feeding the latter is Peterfalvi (10.10)
(`no_typeV_maximal_unconditional`, whose remaining upstream gap is the (6.5) gate, issue
2022), and `T` is type `P` from `T_nonI` (`isTypeP_of_isTypeNonI`). -/
theorem QD_sharp_centralizer_le_T [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∀ z : ↥hyp.T, (z : G) ∈ hyp.Q ⊔ hyp.D → z ≠ 1 →
      Subgroup.centralizer ({(z : G)} : Set G) ≤ hyp.T := by
  intro z hzQD hz1
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hmemA : (z : G) ∈ S10.typePACore hyp.T :=
    hyp.mem_typePACore_of_mem_Q_sup_D _hG hzQD hz1'
  have hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI _hG hyp.T_maximal hyp.T_nonI
  by_contra hesc
  have hz_esc : (z : G) ∈
      OddOrder.GroupTheory.escapingCentralizerSet hyp.T (S10.typePACore hyp.T) :=
    ⟨hmemA, hesc⟩
  rw [escaping_typePACore_eq_empty _hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional _hG) hyp.T_maximal hTP] at hz_esc
  exact Set.notMem_empty _ hz_esc

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

/-- **`T`-instance `u` identity**: the `V`-action image order `chars.u = |V̄| = [V : D] = v`.
Mirror of `mkSection11CharacterDataS_u_eq`, via `cSub = D` and `|V| = v·d`. -/
theorem Hypothesis.mkSection11CharacterDataT_v_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    (hyp.mkSection11CharacterDataT hG hvd chief).u = hyp.v := by
  have hd0 : 0 < hyp.d := hyp.d_eq_card_D ▸ Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hd0 ?_
  have key : (hyp.mkSection11CharacterDataT hG hvd chief).u
      * Nat.card ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
      = Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).U := by
    rw [← OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u
      (hyp.mkSection11CharacterDataT hG hvd chief)]
    have h := Subgroup.index_mul_card
      ((OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief).subgroupOf
        (hyp.toTypesIIIIIIVSetupT hG hvd).U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupT hG hvd) chief)).toEquiv] at h
  rw [hyp.toTypesIIIIIIVSetupT_cSub_eq_D hG hvd chief, ← hyp.d_eq_card_D,
    hyp.toTypesIIIIIIVSetupT_U_eq hG hvd, hyp.card_V_eq_vd] at key
  exact key

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

open scoped FiniteInduce in
/-- **The (13.4) support estimate** (conjunct 2 of the θ-package): for any degree-one
`θ` on `K` and any nonzero row `r`, the difference `Ind_K^T θ − ν_r` is supported in
`(QD)^# = {z ∈ K, z ≠ 1}`.  Both terms are induced from the *normal* `K = QD`
(`nu_i_isIndQD` for the row sum), so they vanish off `K`
(`induce_apply_eq_zero_of_not_mem_normal`); at `1` both have degree
`[T:K]·1 = v·p` (`K_index_eq_vp`), so the difference vanishes. -/
theorem Hypothesis.indK_sub_nuRow_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ) (hθ1 : θ 1 = 1)
    (r : Fin hyp.q) (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) :
    (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
      - ∑ j : Fin hyp.p, hyp.nu r j).support ⊆
      {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1} := by
  have := hyp.finiteG
  let : Fintype ↥hyp.T := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(hyp.K.subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hKn := hyp.K_subgroupOf_T_normal hG
  obtain ⟨θr, hθrirr, hθr1, hθreq⟩ := hyp.nu_i_isIndQD hG pins r hr
  intro z hz
  have hzne : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
      - ∑ j : Fin hyp.p, hyp.nu r j) z ≠ 0 := hz
  refine ⟨?_, ?_⟩
  · -- `(z : G) ∈ Q ⊔ D`: otherwise both inductions vanish at `z`.
    by_contra hzK
    apply hzne
    have hzKsub : z ∉ hyp.K.subgroupOf hyp.T := fun h => hzK (Subgroup.mem_subgroupOf.mp h)
    rw [ClassFunction.sub_apply,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ θ hzKsub, hθreq,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ θr hzKsub,
      sub_zero]
  · -- `z ≠ 1`: at `1` both sides have degree `v·p`.
    intro hz1
    apply hzne
    rw [hz1, ClassFunction.sub_apply, ClassFunction.induce_apply_one, hθ1, mul_one, hθreq,
      ClassFunction.induce_apply_one, hθr1, mul_one, sub_self]

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
/-- **`τ₁T = Ind_T^G` on the `A(T)`-supported span** (mirror of
`tau1S_ofHonest_extends_on_supported`; the (13.2.e) agreement, the conjunct-3 producer of the
(13.4) θ-package): the coherent extension agrees with plain induction on every `A(T)`-supported
lattice element of `ℤ[𝒯]`. -/
theorem Hypothesis.tau1T_ofHonest_extends_on_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (φ : ClassFunction ↥hyp.T ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)) :
    hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief φ
      = ClassFunction.induce hyp.T φ := by
  have h := (hyp.coherentIndT_pinned hG hnoV pins hvd hTP Tdata hU hW1 hW2
    chief).extends_on_supported φ hφ
  simpa [Hypothesis.tau1T_ofHonest, Hypothesis.indT_apply] using h

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(5.3.b)-at-`T` for `τ₁T = tau1T_ofHonest`** (the conjunct-4 producer of the (13.4)
θ-package): the `τ₁T`-image of an irreducible `𝒯`-member is orthogonal to the entire `η`-grid.
The engine `coherentIndT_image_inner_eta_eq_zero` instantiated at the pinned carrier, with the
family inputs discharged from the landed `𝒯`-facts (conjugate-closure, no-real via `|T|` odd,
conjugate-difference `A(T)`-support). -/
theorem Hypothesis.tau1T_ofHonest_image_inner_eta_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    {ζ : ClassFunction ↥hyp.T ℂ} (hζ : ζ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hζirr : IsIrreducibleCharacter ζ) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief ζ)
        (hyp.eta i j) = 0 :=
  coherentIndT_image_inner_eta_eq_zero hG hnoV hyp hTP Tdata hW1 hW2
    (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd))
    (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG))
    (fun ζ' hζ' => by
      rw [show ζ' - ζ'.conj = -(ζ'.conj - ζ') from by abel, ClassFunction.support_neg]
      exact hyp.sSet_member_conjDiff_supported_T hG hvd hζ')
    (hyp.coherentIndT_pinned hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief) hζ hζirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`ℤ[𝒯]`-elements are supported in `A(T) ∪ {1}`** (mirror of `zSpan_sSet_support_subset`):
the `zSpan`-closure of the member-level support fact `sSet_member_support_subset_T`. -/
theorem Hypothesis.zSpan_sSet_support_subset_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {φ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T ∪ {1} := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hyp.sSet_member_support_subset_T hG hvd hx
  | zero => simp
  | add x y _ _ hx hy =>
      exact (ClassFunction.support_add_subset x y).trans (Set.union_subset hx hy)
  | smul z x _ hx =>
      refine subset_trans ?_ hx
      rw [← Int.cast_smul_eq_zsmul ℂ z x]
      exact ClassFunction.support_smul_subset _ x

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Degree-`0` elements of `ℤ[𝒯]` are `A(T)`-supported** (mirror of
`zSpan_sSet_degree_zero_support`; the (13.2.e)-input support step for the
`tau1T_apply_induce_sub` supply). -/
theorem Hypothesis.zSpan_sSet_degree_zero_support_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {φ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd)))
    (hφ1 : φ (1 : ↥hyp.T) = 0) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
  intro z hz
  rcases hyp.zSpan_sSet_support_subset_T hG hvd hφ hz with h | h
  · exact h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact absurd hφ1 hz

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁T`-images of `ℤ[𝒯 ∩ Irr T]` are orthogonal to the `η`-grid** (mirror of
`tau1S_ofHonest_zSpanIrr_inner_eta`): span induction over the (5.3.b)-`T` crux. -/
theorem Hypothesis.tau1T_ofHonest_zSpanIrr_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (i : Fin hyp.q) (j : Fin hyp.p)
    {φ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan
      {ψ : ClassFunction ↥hyp.T ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) ∧
        OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ}) :
    ClassFunction.inner
      (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief φ)
      (hyp.eta i j) = 0 := by
  have := hyp.finiteG
  induction hφ using Submodule.span_induction with
  | mem ζ hζ =>
      exact hyp.tau1T_ofHonest_image_inner_eta_eq_zero hG hnoV pins hvd hTP Tdata hU hW1 hW2
        chief hζ.1 hζ.2 i j
  | zero => rw [map_zero, OddOrder.RepresentationTheory.ClassFunction.inner_zero_left]
  | add x y _ _ hx hy =>
      rw [map_add, OddOrder.RepresentationTheory.ClassFunction.inner_add_left, hx, hy, add_zero]
  | smul z x _ hx =>
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ z,
        OddOrder.RepresentationTheory.ClassFunction.inner_smul_left, hx, mul_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(4.1)+(5.3.b) conjunct-4 producer for the (13.4) θ-package** (mirror of
`tau1S_ofHonest_induce_inner_eta`): for an irreducible `θ` on `K = QD` (`Q ⊄ Ker θ`) whose
induction `Ind_K^T θ` is irreducible, the `τ₁T`-image is orthogonal to the whole `η`-grid.
Composition of the `ℤ[𝒯 ∩ Irr T]` membership (`induce_K_mem_zSpan_sSet_irr_T`) with the
span-level grid orthogonality (`tau1T_ofHonest_zSpanIrr_inner_eta`). -/
theorem Hypothesis.tau1T_ofHonest_induce_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (i : Fin hyp.q) (j : Fin hyp.p)
    (θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθQ : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) :
    ClassFunction.inner (hyp.eta i j)
      (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) = 0 := by
  have := hyp.finiteG
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    hyp.tau1T_ofHonest_zSpanIrr_inner_eta hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief i j
      (hyp.induce_K_mem_zSpan_sSet_irr_T hG pins hvd θ hθ hθQ hind),
    star_zero]

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Differences of degree-one `K`-inductions are supported in `(QD)^#`** (the general-`θ'`
form of `indK_sub_nuRow_support`; the θ-package conjunct-2 companion for the conjugate pair
`Ind_K θ − Ind_K θ̄`): both terms vanish off the normal `K = QD` and share the degree
`[T:K]·1`. -/
theorem Hypothesis.indK_sub_indK_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (θ θ' : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ1 : θ 1 = 1) (hθ'1 : θ' 1 = 1) :
    (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
      - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ').support ⊆
      {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1} := by
  have := hyp.finiteG
  let : Fintype ↥hyp.T := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(hyp.K.subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hKn := hyp.K_subgroupOf_T_normal hG
  intro z hz
  have hzne : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
      - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ') z ≠ 0 := hz
  refine ⟨?_, ?_⟩
  · by_contra hzK
    apply hzne
    have hzKsub : z ∉ hyp.K.subgroupOf hyp.T := fun h => hzK (Subgroup.mem_subgroupOf.mp h)
    rw [ClassFunction.sub_apply,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ θ hzKsub,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ θ' hzKsub, sub_zero]
  · intro hz1
    apply hzne
    rw [hz1, ClassFunction.sub_apply, ClassFunction.induce_apply_one, hθ1,
      ClassFunction.induce_apply_one, hθ'1, sub_self]

open scoped FiniteInduce in
/-- **The (13.2.e) `S`/`T` cross-orthogonality** (the (13.4) disjoint-support input, in
producer form): for an `H^#`-supported `α` on `S` and a `(QD)^#`-supported `β` on `T`, the
inductions to `G` are orthogonal — `(H^#)^G ∩ ((QD)^#)^G = ∅` since every `H^#`-point has
`P ≤ C_G(x)` while `(QD)^#`-centralizers lie in the `T`-conjugates, and no `P`-conjugate lies
in `T`. -/
theorem Hypothesis.inner_induce_H_QD_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {α : ClassFunction ↥hyp.S ℂ}
    (hα : α.support ⊆ {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1})
    {β : ClassFunction ↥hyp.T ℂ}
    (hβ : β.support ⊆ {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1}) :
    ClassFunction.inner (ClassFunction.induce hyp.S α) (ClassFunction.induce hyp.T β) = 0 := by
  have := hyp.finiteG
  have hdisj := disjoint_conjugatesIntoSet_of_centralizer
    (A_M := {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1})
    (A_N := {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1})
    (fun _y hy => hyp.P_le_centralizer_of_mem_H hG hy.1)
    (fun z hz => QD_sharp_centralizer_le_T hG hyp z hz.1 hz.2)
    (P_conj_forall_not_le_T hG hyp)
  exact inner_induce_induce_eq_zero_of_disjoint hα hβ hdisj

open scoped FiniteInduce in
/-- **Differences of degree-one `H`-inductions are supported in `H^#`** (the `S`-side mirror
of `indK_sub_indK_support`; the (13.4) `α`-support for the conjugate pair `λ − λ̄`). -/
theorem Hypothesis.indH_sub_indH_support [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ1 : θ 1 = 1) (hθ'1 : θ' 1 = 1) :
    (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ').support ⊆
      {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1} := by
  have := hyp.finiteG
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hHn : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
  intro y hy
  have hyne : (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') y ≠ 0 := hy
  refine ⟨?_, ?_⟩
  · by_contra hyH
    apply hyne
    have hyHsub : y ∉ hyp.H.subgroupOf hyp.S := fun h => hyH (Subgroup.mem_subgroupOf.mp h)
    rw [ClassFunction.sub_apply,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ θ hyHsub,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ θ' hyHsub, sub_zero]
  · intro hy1
    apply hyne
    rw [hy1, ClassFunction.sub_apply, ClassFunction.induce_apply_one, hθ1,
      ClassFunction.induce_apply_one, hθ'1, sub_self]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The no-θ (Galois) branch of the `T`-side (13.3.b) facts**: if `𝒯` contains no
`vp`-degree `QD`-induced irreducible (`¬ ThetaWitness`), then `M = T` is in case (9.7.b)
with `D = ⊥` and `v = (q^p−1)/(q−1)`.  Mirror of `S_caseB_facts_no_lambda` (whose
`hbridge`/`hno` shape it reproduces verbatim on the `T`-instance). -/
theorem Hypothesis.T_caseB_facts_no_theta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hnotheta : ¬ ThetaWitness hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) := by
  have := hyp.finiteG
  have hvd : hyp.v * hyp.d ≠ 1 := hyp.vd_ne_one hG
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupT hG hvd)
  have hbridge : ∀ χ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ → ThetaWitness hyp := by
    intro χ _hχmem _hχirr
    rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataT hG hvd chief) with hA | hB
    · obtain ⟨caseA⟩ := hA
      exact hyp.thetaWitness_of_caseA hG hvd chief caseA
    · obtain ⟨caseB⟩ := hB
      exact hyp.thetaWitness_of_caseB_member hG hvd chief caseB _hχmem _hχirr
  have hno : ¬ ∃ χ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    fun ⟨χ, hmem, hirr⟩ => hnotheta (hbridge χ hmem hirr)
  obtain ⟨-, hDbot, hvfull⟩ :=
    caseB_of_no_irreducible_sOf_H0Cprime hG
      (hyp.mkSection11CharacterDataT hG hvd chief) hno
  refine ⟨?_, ?_⟩
  · rw [← hyp.toTypesIIIIIIVSetupT_cSub_eq_D hG hvd chief]
    exact hDbot
  · rw [← hyp.mkSection11CharacterDataT_v_eq hG hvd chief, hvfull,
      hyp.chiefFactorT_p_eq hG hvd chief, hyp.toTypesIIIIIIVSetupT_q_eq hG hvd]

/-- **The (13.4) θ-supply**: if `T` is *not* in the (9.7.b) Galois case (the `_hne` of
`tSide_theta_package_of_not_caseB_core`), then `𝒯` contains a `vp`-degree `QD`-linear
induced irreducible.  Contrapositive of `T_caseB_facts_no_theta` + the unconditional
`card_Q_eq_qp` (the third conjunct is always true, so `_hne` reduces to
`¬(D = ⊥ ∧ v = full)`). -/
theorem Hypothesis.thetaWitness_of_not_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hne : ¬ (hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p)) : ThetaWitness hyp := by
  by_contra hno
  obtain ⟨hD, hv⟩ := hyp.T_caseB_facts_no_theta hG hno
  exact hne ⟨hD, hv, hyp.card_Q_eq_qp hG⟩

open scoped FiniteInduce in
/-- **(13.3.b,c)-for-`T` θ-package, Core/λ-cluster form** ((13.4) character gate — the
core/lam restatement of `tSide_theta_package_of_not_caseB`, issue 9094 案 A).

**Residual (precisely named, mirrors the legacy sorried gate)**: the T-side (13.3.b)/(13.3.c)
package — `𝒯` contains an irreducible `θ` induced from a linear character of `K = QD`, the
`ν`-row τ₁-formula, and the pairwise orthogonality of `η`, `λ^{τ₁}`, `θ^{τ₁}`.  Gated on the
ν-side grid supply (`nuGridSupply`) and the `T`-side coherence — the swap-instance of the
S-side (13.3) engines (issue 9013 追記⁶). -/
theorem _root_.solution [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (pins : NuGridSupplyData hyp)
    (_hne : ¬ (hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p)) :
    ∃ (θT : ClassFunction ↥hyp.T ℂ) (r r' : Fin hyp.q) (δ' : ℤ) (θG : ClassFunction G ℂ),
      (δ' = 1 ∨ δ' = -1) ∧
      ((θT - ∑ j : Fin hyp.p, hyp.nu r j).support ⊆
        {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1}) ∧
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)
        = θG - (δ' : ℂ) • ∑ j : Fin hyp.p, hyp.eta r' j) ∧
      (∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) θG = 0) ∧
      ClassFunction.inner (core.tau1S lam.lambda) θG = 0 := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.T := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(hyp.K.subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- ── supply: the Hypothesis-level producers
  have hnoV := OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional _hG
  have hvd : hyp.v * hyp.d ≠ 1 := hyp.vd_ne_one _hG
  have hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T := hyp.T_isTypeP _hG
  obtain ⟨Tdata, hU, hW1, hW2⟩ := reconciled_typePData_T _hG hyp
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData _hG
    (hyp.toTypesIIIIIIVSetupT _hG hvd)
  -- ── the (13.3.b)-at-`T` θ-witness
  obtain ⟨θ, hθirr, hθ1, hθQ, hind⟩ := hyp.thetaWitness_of_not_caseB _hG _hne
  have hq1 : (⟨1, hyp.q_prime.one_lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  -- ── the (13.3.c)-at-`T` pin at the anchor row `1`
  obtain ⟨r', δ', hr'0, hδ', hpin⟩ :=
    hyp.tau1T_ofHonest_nuRow_eta_row _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief hq1
  refine ⟨ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ, ⟨1, hyp.q_prime.one_lt⟩, r', δ',
    hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ),
    hδ', ?_, ?_, ?_, ?_⟩
  · -- conjunct 2: the (13.4) support estimate
    exact hyp.indK_sub_nuRow_support _hG pins θ hθ1 ⟨1, hyp.q_prime.one_lt⟩ hq1
  · -- conjunct 3: `Ind_T(θ_T − ν₁) = θ_G − δ'·∑_j η_{r'j}` ((13.2.e) agreement + the pin)
    have hzspan : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
          - ∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
        ∈ OddOrder.Peterfalvi.S07.zSpan
            (OddOrder.Peterfalvi.S11.sSet (hyp.toTypesIIIIIIVSetupT _hG hvd)) :=
      Submodule.sub_mem _ (hyp.induce_K_mem_zSpan_T _hG hvd θ hθirr hθQ)
        (Submodule.subset_span (OddOrder.Peterfalvi.S11.sOf_subset_sSet _ chief.H0
          (hyp.nu_rowSum_mem_sOf_H0_T _hG pins hvd chief ⟨1, hyp.q_prime.one_lt⟩ hq1)))
    have hdeg0 : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
        - ∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j) (1 : ↥hyp.T) = 0 := by
      obtain ⟨θr, hθrirr, hθr1, hθreq⟩ :=
        hyp.nu_i_isIndQD _hG pins ⟨1, hyp.q_prime.one_lt⟩ hq1
      rw [ClassFunction.sub_apply, hθreq,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθr1, sub_self]
    have hext := hyp.tau1T_ofHonest_extends_on_supported _hG hnoV pins hvd hTP Tdata hU hW1
      hW2 chief _ ⟨hzspan, hyp.zSpan_sSet_degree_zero_support_T _hG hvd hzspan hdeg0⟩
    rw [← hext, map_sub, hpin]
  · -- conjunct 4: `θ_G ⊥ η`-grid ((4.1)+(5.3.b)-at-`T`)
    intro i j
    exact hyp.tau1T_ofHonest_induce_inner_eta _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
      i j θ hθirr hθQ hind
  · -- conjunct 5: `⟨λ^{τ₁S}, θ^{τ₁T}⟩ = 0` (the (13.4) pairwise orthogonality)
    obtain ⟨thetaL, hthetaLirr, hthetaL1, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
      lam.lambda_induced_from_PC_linear
    have hthetaLP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel thetaL) := by
      intro hsub
      exact hx₀ker (hsub (by
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact hx₀P))
    -- ── `S`-side conjugate data
    have hthetaLc1 : thetaL.conj 1 = 1 := by
      rw [ClassFunction.conj_apply, hthetaL1, star_one]
    have hthetaLPc : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel thetaL.conj) := by
      rw [OddOrder.Peterfalvi.S03.characterKernel_conj]
      exact hthetaLP
    have hlamconj : lam.lambda.conj
        = ClassFunction.induce (hyp.H.subgroupOf hyp.S) thetaL.conj := by
      rw [hlamEq, OddOrder.RepresentationTheory.ClassFunction.induce_conj]
    -- ── `λ` is non-real (odd `|S|`, degree `u·q ≠ 1`)
    have hu_ne : hyp.u ≠ 0 := by
      intro h0
      have hcard : 0 < Nat.card ↥hyp.U := Nat.card_pos
      rw [hyp.card_U_eq_uc, h0, zero_mul] at hcard
      exact absurd hcard (lt_irrefl 0)
    have hlamdeg : lam.lambda 1 = ((hyp.u * hyp.q : ℕ) : ℂ) := by
      rw [hlamEq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hthetaL1,
        mul_one, hyp.H_index_eq_uq _hG]
    have hlamNR : ¬ ClassFunction.IsReal lam.lambda := by
      have hne : (⟨lam.lambda, lam.lambda_irreducible⟩ : IrreducibleCharacter ↥hyp.S)
          ≠ trivialIrreducibleCharacter ↥hyp.S := by
        intro h
        have h1 := congrArg (fun ξ : IrreducibleCharacter ↥hyp.S =>
          (ξ : ClassFunction ↥hyp.S ℂ) (1 : ↥hyp.S)) h
        simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter] at h1
        rw [hlamdeg] at h1
        have h2 : (hyp.u * hyp.q : ℕ) = 1 := by
          have h3 : ((hyp.u * hyp.q : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
            rw [h1]; norm_num
          exact_mod_cast h3
        have h3q := hyp.three_le_q
        have hqd : hyp.q ∣ 1 := ⟨hyp.u, by rw [← h2]; ring⟩
        have := Nat.le_of_dvd one_pos hqd
        omega
      exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
        (hyp.oddCardS _hG) hne
    have hAB0 : ClassFunction.inner lam.lambda lam.lambda.conj = 0 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner lam.lambda_irreducible
        lam.lambda_irreducible.conj, if_neg (fun h => hlamNR h.symm)]
    -- ── `S`-side dirr inputs via the Core fields
    have hAZ : core.tau1S lam.lambda ∈ ZIrr G := by
      rw [hlamEq]
      exact core.tau1S_induce_mem_ZIrr thetaL hthetaLirr hthetaLP
    have hBZ : core.tau1S lam.lambda.conj ∈ ZIrr G := by
      rw [hlamconj]
      exact core.tau1S_induce_mem_ZIrr thetaL.conj hthetaLirr.conj hthetaLPc
    have hA1 : ClassFunction.inner (core.tau1S lam.lambda) (core.tau1S lam.lambda) = 1 := by
      conv_lhs => rw [hlamEq]
      rw [core.tau1S_inner_induce thetaL thetaL hthetaLirr hthetaLirr hthetaLP hthetaLP,
        ← hlamEq]
      exact lam.lambda_irreducible.inner_self_eq_one
    have hB1 : ClassFunction.inner (core.tau1S lam.lambda.conj)
        (core.tau1S lam.lambda.conj) = 1 := by
      conv_lhs => rw [hlamconj]
      rw [core.tau1S_inner_induce thetaL.conj thetaL.conj hthetaLirr.conj hthetaLirr.conj
        hthetaLPc hthetaLPc, ← hlamconj]
      exact lam.lambda_irreducible.conj.inner_self_eq_one
    have hABi : ClassFunction.inner (core.tau1S lam.lambda)
        (core.tau1S lam.lambda.conj) = 0 := by
      conv_lhs => rw [hlamconj, hlamEq]
      rw [core.tau1S_inner_induce thetaL thetaL.conj hthetaLirr hthetaLirr.conj hthetaLP
        hthetaLPc, ← hlamEq, ← hlamconj]
      exact hAB0
    have hABdiff : core.tau1S lam.lambda - core.tau1S lam.lambda.conj
        = ClassFunction.induce hyp.S (lam.lambda - lam.lambda.conj) := by
      rw [← map_sub]
      conv_lhs => rw [hlamconj, hlamEq]
      rw [core.tau1S_apply_induce_sub thetaL thetaL.conj hthetaLirr hthetaLirr.conj
        hthetaLP hthetaLPc, ← hlamEq, ← hlamconj]
    have hBAdiff : core.tau1S lam.lambda.conj - core.tau1S lam.lambda
        = ClassFunction.induce hyp.S (lam.lambda.conj - lam.lambda) := by
      rw [← map_sub]
      conv_lhs => rw [hlamconj, hlamEq]
      rw [core.tau1S_apply_induce_sub thetaL.conj thetaL hthetaLirr.conj hthetaLirr
        hthetaLPc hthetaLP, ← hlamEq, ← hlamconj]
    have hABconj : (core.tau1S lam.lambda).conj - (core.tau1S lam.lambda.conj).conj
        = core.tau1S lam.lambda.conj - core.tau1S lam.lambda := by
      rw [← ClassFunction.conj_sub, hABdiff, hBAdiff,
        OddOrder.RepresentationTheory.ClassFunction.induce_conj]
      congr 1
      rw [ClassFunction.conj_sub, ClassFunction.conj_conj]
    -- ── `T`-side conjugate data
    have hθc1 : θ.conj 1 = 1 := by
      rw [ClassFunction.conj_apply, hθ1, star_one]
    have hθQc : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ.conj) := by
      rw [OddOrder.Peterfalvi.S03.characterKernel_conj]
      exact hθQ
    have hindconjeq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj
        = (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ).conj :=
      (OddOrder.RepresentationTheory.ClassFunction.induce_conj _ _).symm
    have hindc : OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) := by
      rw [hindconjeq]
      exact hind.conj
    -- ── `θ_T` is non-real (odd `|T|`, degree `v·p ≠ 1`)
    have hv_ne : hyp.v ≠ 0 := by
      intro h0
      have hcard : 0 < Nat.card ↥hyp.V := Nat.card_pos
      rw [hyp.card_V_eq_vd, h0, zero_mul] at hcard
      exact absurd hcard (lt_irrefl 0)
    have hθTdeg : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ (1 : ↥hyp.T)
        = ((hyp.v * hyp.p : ℕ) : ℂ) := by
      rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one,
        hyp.K_index_eq_vp _hG]
    have hθTNR : ¬ ClassFunction.IsReal
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) := by
      have hne : (⟨ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ, hind⟩ :
          IrreducibleCharacter ↥hyp.T) ≠ trivialIrreducibleCharacter ↥hyp.T := by
        intro h
        have h1 := congrArg (fun ξ : IrreducibleCharacter ↥hyp.T =>
          (ξ : ClassFunction ↥hyp.T ℂ) (1 : ↥hyp.T)) h
        simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter] at h1
        rw [hθTdeg] at h1
        have h2 : (hyp.v * hyp.p : ℕ) = 1 := by
          have h3 : ((hyp.v * hyp.p : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
            rw [h1]; norm_num
          exact_mod_cast h3
        have h3p := hyp.three_le_p
        have hpd : hyp.p ∣ 1 := ⟨hyp.v, by rw [← h2]; ring⟩
        have := Nat.le_of_dvd one_pos hpd
        omega
      exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
        (hyp.oddCardT _hG) hne
    have hCD0 : ClassFunction.inner (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) = 0 := by
      rw [hindconjeq, OddOrder.RepresentationTheory.irr_cf_inner hind hind.conj,
        if_neg (fun h => hθTNR h.symm)]
    -- ── `T`-side dirr inputs via the pinned coherence carrier
    have hmemθ := hyp.induce_K_mem_zSpan_T _hG hvd θ hθirr hθQ
    have hmemθc := hyp.induce_K_mem_zSpan_T _hG hvd θ.conj hθirr.conj hθQc
    have hCZ : hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) ∈ ZIrr G :=
      (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
        chief).extension_mem_ZIrr _ hmemθ
    have hDZ : hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) ∈ ZIrr G :=
      (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
        chief).extension_mem_ZIrr _ hmemθc
    have hC1 : ClassFunction.inner
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ))
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) = 1 := by
      rw [show (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ))
          = (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
            chief).extension (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) from rfl,
        (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
          chief).extension_inner_eq _ _ hmemθ hmemθ]
      exact hind.inner_self_eq_one
    have hD1 : ClassFunction.inner
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj))
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)) = 1 := by
      rw [show (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj))
          = (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
            chief).extension (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) from rfl,
        (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
          chief).extension_inner_eq _ _ hmemθc hmemθc]
      exact hindc.inner_self_eq_one
    have hCDi : ClassFunction.inner
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ))
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)) = 0 := by
      rw [show (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ))
          = (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
            chief).extension (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) from rfl,
        show (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj))
          = (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
            chief).extension (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) from rfl,
        (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
          chief).extension_inner_eq _ _ hmemθ hmemθc]
      exact hCD0
    -- ── the `T`-side difference is the honest induction ((13.2.e))
    have hCDzspan : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
          - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)
        ∈ OddOrder.Peterfalvi.S07.zSpan
            (OddOrder.Peterfalvi.S11.sSet (hyp.toTypesIIIIIIVSetupT _hG hvd)) :=
      Submodule.sub_mem _ hmemθ hmemθc
    have hCDdeg0 : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
        - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) (1 : ↥hyp.T) = 0 := by
      rw [ClassFunction.sub_apply,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθc1, sub_self]
    have hCDdiff : hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
        - hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)
        = ClassFunction.induce hyp.T
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
              - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) := by
      rw [← map_sub]
      exact hyp.tau1T_ofHonest_extends_on_supported _hG hnoV pins hvd hTP Tdata hU hW1 hW2
        chief _ ⟨hCDzspan, hyp.zSpan_sSet_degree_zero_support_T _hG hvd hCDzspan hCDdeg0⟩
    have hDCdiff : hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)
        - hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
        = ClassFunction.induce hyp.T
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj
              - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) := by
      rw [← map_sub]
      refine hyp.tau1T_ofHonest_extends_on_supported _hG hnoV pins hvd hTP Tdata hU hW1 hW2
        chief _ ⟨Submodule.sub_mem _ hmemθc hmemθ,
          hyp.zSpan_sSet_degree_zero_support_T _hG hvd (Submodule.sub_mem _ hmemθc hmemθ) ?_⟩
      rw [ClassFunction.sub_apply,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθc1,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, sub_self]
    have hCDconj : (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)).conj
        - (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)).conj
        = hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)
          - hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) := by
      rw [← ClassFunction.conj_sub, hCDdiff, hDCdiff,
        OddOrder.RepresentationTheory.ClassFunction.induce_conj]
      congr 1
      rw [ClassFunction.conj_sub, hindconjeq, ClassFunction.conj_conj]
    -- ── the (13.2.e) disjoint-support cross input
    have hαsupp : (lam.lambda - lam.lambda.conj).support ⊆
        {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1} := by
      rw [hlamconj, hlamEq]
      exact hyp.indH_sub_indH_support _hG thetaL thetaL.conj hthetaL1 hthetaLc1
    have hβsupp : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
        - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj).support ⊆
        {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1} :=
      hyp.indK_sub_indK_support _hG θ θ.conj hθ1 hθc1
    have h0 : ClassFunction.inner
        (core.tau1S lam.lambda - core.tau1S lam.lambda.conj)
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
          - hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)) = 0 := by
      rw [hABdiff, hCDdiff]
      exact hyp.inner_induce_H_QD_eq_zero _hG hαsupp hβsupp
    -- ── the dirr brick closes conjunct 5
    exact inner_eq_zero_of_conj_diff_orthogonal hAZ hBZ hCZ hDZ hA1 hB1 hC1 hD1 hABi hCDi
      hABconj hCDconj h0

end OddOrder.Peterfalvi.S15
