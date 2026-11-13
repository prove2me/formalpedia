-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.normalizer_U_inf_W2_eq_bot_of_data_and_c_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:02.219332+00:00
-- url     : https://prove2.me/submissions/98208e7c-7c5b-42f1-9a54-8ffb80ed825d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndTDefs.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
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
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient

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

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- **`C = ⊥` from (13.12)** — the subgroup-level form of the regularity `c = 1`
(Coq `FTtypeP_reg_Fcore`).  The explicit input keeps downstream (13.18) consumers independent of
the legacy character-degree carrier. -/
theorem Hypothesis.C_eq_bot_of_c_eq_one [Finite G] (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) : hyp.C = ⊥ :=
  Subgroup.card_eq_one.mp (by rw [← hyp.c_eq_card_C]; exact hc1)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndTDefs.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.12) `c = 1`, usable form**: `U ⊓ C_G(P) = ⊥` — no nonidentity element of the
complement `U` centralizes the Fitting kernel `P = S_F` (`U` acts faithfully on `P`).  Immediate
from
`C_eq_bot` and `C = U ⊓ C_G(P)` (`C_eq`).  The Maschke/Wielandt core of (13.16) concludes
`N_U(W₂) ≤ U ⊓ C_G(P) = ⊥`. -/
theorem U_inf_centralizer_P_eq_bot_of_c_eq_one [Finite G]
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    hyp.U ⊓ Subgroup.centralizer (hyp.P : Set G) = ⊥ := by
  rw [← hyp.C_eq]
  exact hyp.C_eq_bot_of_c_eq_one hc1

/-- **Peterfalvi (13.16), Frobenius fixed-point-freeness of `W₁` on `U`**: `C_U(W₁) = ⊥` — no
nonidentity element of the complement `U` centralizes `W₁`.

Immediate from the `U ⋊ W₁` Frobenius structure (`BasicStructureData.UW1_frobenius`,
`IsFrobeniusGroup.conj_frobenius`): a nonidentity `x ∈ U` centralizing a nonidentity `w ∈ W₁` would
give `w x w⁻¹ = x`, contradicting the Frobenius condition (the complement acts fixed-point-freely on
the kernel).  This is the `C_K(W₁) ≤ C_U(W₁) = ⊥` input to the (13.16) core
`normalizer_U_inf_W2_eq_bot` (the coprime fixed-point lifting of the crux `K ≤ C_G(W₂)`). -/
theorem centralizer_W1_inf_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.U ⊓ Subgroup.centralizer (hyp.W1 : Set G) = ⊥ := by
  obtain ⟨data, _⟩ := basic_structure hG hyp
  have hfrob := data.UW1_frobenius
  -- a nonidentity `w ∈ W₁` (`|W₁| = q` prime).
  have hW1ne : hyp.W1 ≠ ⊥ := by
    intro hbot
    have hq1 : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hbot, Subgroup.card_bot]
    exact hyp.q_prime.one_lt.ne' hq1
  have : Nontrivial ↥hyp.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW1ne
  obtain ⟨w0, hw0⟩ := exists_ne (1 : ↥hyp.W1)
  set w : G := (w0 : G) with hw
  have hwW1 : w ∈ hyp.W1 := w0.2
  have hwne : w ≠ 1 := fun h => hw0 (OneMemClass.coe_eq_one.mp (hw ▸ h))
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxU, hxC⟩ := hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  -- lift `w, x` to `↥(U ⊔ W₁)` and apply `conj_frobenius`.
  have hxUW1 : x ∈ hyp.U ⊔ hyp.W1 := Subgroup.mem_sup_left hxU
  have hwUW1 : w ∈ hyp.U ⊔ hyp.W1 := Subgroup.mem_sup_right hwW1
  have hxN : (⟨x, hxUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.U.subgroupOf (hyp.U ⊔ hyp.W1) := by
    rw [Subgroup.mem_subgroupOf]; exact hxU
  have hwA : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1) := by
    rw [Subgroup.mem_subgroupOf]; exact hwW1
  have hxN1 : (⟨x, hxUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 :=
    fun h => hx1 (by simpa using congrArg (Subgroup.subtype _) h)
  have hwA1 : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 :=
    fun h => hwne (by simpa using congrArg (Subgroup.subtype _) h)
  have hcomm : w * x = x * w := (Subgroup.mem_centralizer_iff.mp hxC) w hwW1
  exact hfrob.conj_frobenius _ hwA hwA1 _ hxN hxN1 (by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [hcomm]; group)

/-- **Peterfalvi (13.16), `W₁`-triviality on `K/C_K(W₂)`**: for `g ∈ N_G(W₂)` and `w ∈ W₁`, the
"twisted commutator" `g⁻¹ (w g w⁻¹) ∈ C_G(W₂)` — conjugating `g` by `w ∈ W₁ ≤ C_G(W₂)` changes it
only by an element centralizing `W₂`.

Since `w` centralizes `W₂` (`W = W₁ × W₂` abelian) and `g` normalizes `W₂`, the elements `w g w⁻¹`
and `g` induce the **same** conjugation on `W₂` (`w` fixes `g y g⁻¹ ∈ W₂`), so
`g⁻¹ (w g w⁻¹)` centralizes `W₂`.  This is the "`W₁` acts trivially on `K/C_K(W₂)`" input to the
coprime fixed-point lifting (`coprime_fixedPoints_quotient`) of the crux `K ≤ C_G(W₂)` in
`normalizer_U_inf_W2_eq_bot`. -/
theorem conj_W1_mem_centralizer_W2 [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {g : G} (hg : g ∈ Subgroup.normalizer (hyp.W2 : Set G))
    {w : G} (hw : w ∈ hyp.W1) :
    g⁻¹ * (w * g * w⁻¹) ∈ Subgroup.centralizer (hyp.W2 : Set G) := by
  -- `w` centralizes `W₂`.
  have hwC : ∀ z ∈ hyp.W2, w * z = z * w := fun z hz => hyp.W1_commutes_W2 w hw z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyW2 : y ∈ hyp.W2 := hy
  -- `g y g⁻¹ ∈ W₂`.
  have hy1 : g * y * g⁻¹ ∈ hyp.W2 := (Subgroup.mem_normalizer_iff.mp hg y).mp hyW2
  -- `w⁻¹ y w = y` and `w (g y g⁻¹) w⁻¹ = g y g⁻¹`.
  have h1 : w⁻¹ * y * w = y := by
    rw [mul_assoc, ← hwC y hyW2, inv_mul_cancel_left]
  have h2 : w * (g * y * g⁻¹) * w⁻¹ = g * y * g⁻¹ := by
    rw [hwC _ hy1, mul_assoc, mul_inv_cancel, mul_one]
  -- `w g w⁻¹` and `g` induce the same conjugation on `y`.
  have hsame : (w * g * w⁻¹) * y * (w * g * w⁻¹)⁻¹ = g * y * g⁻¹ := by
    calc (w * g * w⁻¹) * y * (w * g * w⁻¹)⁻¹
        = w * g * (w⁻¹ * y * w) * g⁻¹ * w⁻¹ := by group
      _ = w * g * y * g⁻¹ * w⁻¹ := by rw [h1]
      _ = w * (g * y * g⁻¹) * w⁻¹ := by group
      _ = g * y * g⁻¹ := h2
  -- hence `n' := g⁻¹ (w g w⁻¹)` fixes `y`.
  have hn' : (g⁻¹ * (w * g * w⁻¹)) * y * (g⁻¹ * (w * g * w⁻¹))⁻¹ = y := by
    calc (g⁻¹ * (w * g * w⁻¹)) * y * (g⁻¹ * (w * g * w⁻¹))⁻¹
        = g⁻¹ * ((w * g * w⁻¹) * y * (w * g * w⁻¹)⁻¹) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hsame]
      _ = y := by group
  exact (mul_inv_eq_iff_eq_mul.mp hn').symm

/-- **Peterfalvi (13.16), the crux `K ≤ C_G(W₂)`**: every element of `K := U ⊓ N_G(W₂)` centralizes
`W₂`.

The conjugation action of `W₁` on the abelian `U` is coprime (`(|W₁|, |U|) = 1` from the `U ⋊ W₁`
Frobenius structure) with fixed points `C_U(W₁) = ⊥` (`centralizer_W1_inf_U_eq_bot`).  For `g ∈ K`,
`W₁` fixes the coset `g · C_U(W₂)` (`conj_W1_mem_centralizer_W2`: `g⁻¹ (w g w⁻¹) ∈ C_G(W₂)`), so the
coprime fixed-point lifting `Isaacs.Ch04.coprime_fixedPoints_quotient` (Cor 3.28) produces a
`W₁`-fixed representative `c ∈ C_U(W₁) = ⊥`; hence `g ≡ 1 (mod C_U(W₂))`, i.e. `g ∈ C_G(W₂)`. -/
theorem normalizer_U_inf_W2_le_centralizer_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.U ⊓ Subgroup.normalizer (hyp.W2 : Set G) ≤ Subgroup.centralizer (hyp.W2 : Set G) := by
  obtain ⟨data, _⟩ := basic_structure hG hyp
  have hfrob := data.UW1_frobenius
  have hUcomm := data.U_commutative
  -- conjugation action `φ : ↥W₁ → MulAut ↥U`.
  let actU : MulDistribMulAction ↥hyp.W1 ↥hyp.U :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (hyp.U : Set G))) ↥hyp.U
      (Subgroup.inclusion hyp.W1_normalizes_U)
  set φ : ↥hyp.W1 →* MulAut ↥hyp.U := MulDistribMulAction.toMulAut ↥hyp.W1 ↥hyp.U with hφ
  have hφ_coe : ∀ (a : ↥hyp.W1) (x : ↥hyp.U),
      (hyp.U.subtype ((φ a) x)) = (↑a) * (hyp.U.subtype x) * (↑a)⁻¹ := fun _ _ => rfl
  -- `N := C_U(W₂)`, normal in the abelian `↥U`.
  set N : Subgroup ↥hyp.U :=
    (hyp.U ⊓ Subgroup.centralizer (hyp.W2 : Set G)).subgroupOf hyp.U with hN_def
  have hNnorm : N.Normal := by
    refine ⟨fun n _ g => ?_⟩
    have hc : g * n * g⁻¹ = n := by rw [mul_comm' g n, mul_inv_cancel_right]
    rw [hc]; assumption
  -- coprimality `(|W₁|, |U|) = 1`.
  have hCop : Nat.Coprime (Nat.card ↥hyp.W1) (Nat.card ↥hyp.U) := by
    have hk := hfrob.coprime_card_kernel_complement
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
      Nat.coprime_comm] at hk
  -- `W₁ ≤ C_G(W₂)`, so `N` is `W₁`-invariant.
  have hW1_le_C : hyp.W1 ≤ Subgroup.centralizer (hyp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hyp.W1_commutes_W2 x hx z hz).symm
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [hN_def, Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨_, hxC⟩ := Subgroup.mem_inf.mp hx
    have hval : (hyp.U.subtype ((φ a) x)) = (↑a) * (hyp.U.subtype x) * (↑a)⁻¹ := hφ_coe a x
    refine Subgroup.mem_inf.mpr ⟨((φ a) x).2, ?_⟩
    rw [show ((φ a) x : G) = (hyp.U.subtype ((φ a) x)) from rfl, hval]
    exact (Subgroup.centralizer (hyp.W2 : Set G)).mul_mem
      (Subgroup.mul_mem _ (hW1_le_C a.2) hxC) (Subgroup.inv_mem _ (hW1_le_C a.2))
  -- main: `g ∈ U ⊓ N_G(W₂)` ⟹ `g ∈ C_G(W₂)`.
  intro g hg
  obtain ⟨hgU, hgNW2⟩ := Subgroup.mem_inf.mp hg
  set gg : ↥hyp.U := ⟨g, hgU⟩ with hgg
  -- `W₁` fixes the coset `gg · N`.
  have hg_fix : ∀ a : ↥hyp.W1, ∃ n ∈ N, (φ a) gg = gg * n := by
    intro a
    refine ⟨gg⁻¹ * (φ a) gg, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [hN_def, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨(gg⁻¹ * (φ a) gg).2, ?_⟩
    have hval : ((gg⁻¹ * (φ a) gg : ↥hyp.U) : G) = g⁻¹ * ((a : G) * g * (a : G)⁻¹) := by
      rw [Subgroup.coe_mul, InvMemClass.coe_inv,
        show ((φ a) gg : G) = (hyp.U.subtype ((φ a) gg)) from rfl, hφ_coe a gg]
      rfl
    rw [hval]
    exact conj_W1_mem_centralizer_W2 hG hyp hgNW2 a.2
  obtain ⟨c, hc_fix, m, hm, hc_eq⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (φ := φ) hCop
      (Or.inr (Group.isSolvable_of_comm (fun a b => mul_comm' a b))) hN_inv hg_fix
  -- `c` is `W₁`-fixed ⟹ `(c:G) ∈ C_U(W₁) = ⊥` ⟹ `c = 1`.
  have hc1 : c = 1 := by
    have hcmem : (c : G) ∈ hyp.U ⊓ Subgroup.centralizer (hyp.W1 : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hfix := hc_fix ⟨w, hw⟩
      have hco : (hyp.U.subtype c) = (w : G) * (hyp.U.subtype c) * (w : G)⁻¹ := by
        have e1 := hφ_coe ⟨w, hw⟩ c
        rw [hfix] at e1
        exact e1
      exact mul_inv_eq_iff_eq_mul.mp hco.symm
    rw [centralizer_W1_inf_U_eq_bot hG hyp, Subgroup.mem_bot] at hcmem
    exact Subtype.ext hcmem
  -- `gg = m⁻¹ ∈ N` ⟹ `g ∈ C_G(W₂)`.
  rw [hc1, eq_comm, mul_eq_one_iff_eq_inv] at hc_eq
  have hggN : gg ∈ N := by rw [hc_eq]; exact N.inv_mem hm
  rw [hN_def, Subgroup.mem_subgroupOf] at hggN
  exact (Subgroup.mem_inf.mp hggN).2

/-- **Peterfalvi (13.16), the core assembly** (`U ⊓ N_G(W₂) = ⊥`, modulo the two §16-carrier data).

Given the (13.2) faithfulness data `hdisj : P ⊓ U = ⊥` (yielding `Coprime |U| |P|`) and the type-`P`
reconciliation `hrec : Sdata.W2 = W2`, the assembly closes the core from the proven crux
`K ≤ C_G(W₂)` (`normalizer_U_inf_W2_le_centralizer_W2`):

* the coprime `K`-action on the abelian `P` decomposes `P = (C_G(K) ⊓ P) ⊕ ⁅P, K⁆`
  (`Isaacs.Ch05.fitting_coprime_abelian_decomp`, Gorenstein Thm 2.3);
* `W₁` acts fixed-point-freely on `⁅P, K⁆`: any `W₁`-fixed `n ∈ ⁅P, K⁆ ⊆ P` lies in
  `M' ⊓ C_G(x) = Sdata.W2 = W₂` (`TypePData.centralizer_W1` + `hrec`) `⊆ C_G(K) ⊓ P` (crux), so
  `n ∈ (C_G(K) ⊓ P) ⊓ ⁅P, K⁆ = ⊥`;
* the full `U ⋊ W₁` Frobenius (`UW1_frobenius`; `U` abelian ⟹ `U ≤ N_G(⁅P,K⁆)`) then centralizes
  `⁅P, K⁆` by Wielandt (`frobenius_kernel_centralizes_of_complement_fpf`);
* so `⁅P, K⁆ ≤ C_G(U) ∩ P ≤ C_G(K) ⊓ P`, whence `⁅P, K⁆ = ⊥`, i.e. `K ≤ C_G(P)`, giving
  `K ≤ U ⊓ C_G(P) = ⊥` (`U_inf_centralizer_P_eq_bot`). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1)
    (hcop : Nat.Coprime (Nat.card ↥hyp.P) (Nat.card ↥(hyp.U ⊔ hyp.W1)))
    (hrec : hyp.Sdata.W2 = hyp.W2) :
    hyp.U ⊓ Subgroup.normalizer (hyp.W2 : Set G) = ⊥ := by
  obtain ⟨data, _, hP_elemAb, _, _, _⟩ := basic_structure hG hyp
  have hUcomm := data.U_commutative
  set K := hyp.U ⊓ Subgroup.normalizer (hyp.W2 : Set G) with hK_def
  have hK_le_U : K ≤ hyp.U := inf_le_left
  -- crux: `K ≤ C_G(W₂)`.
  have hKC : K ≤ Subgroup.centralizer (hyp.W2 : Set G) :=
    normalizer_U_inf_W2_le_centralizer_W2 hG hyp
  -- `P` abelian.
  have hPcomm : IsMulCommutative ↥hyp.P := IsMulCommutative.of_comm hP_elemAb.comm
  -- divisibilities `|K| ∣ |U| ∣ |U⋊W₁|`, from the coprime-action datum `hcop`.
  have hUdvdUW1 : Nat.card ↥hyp.U ∣ Nat.card ↥(hyp.U ⊔ hyp.W1) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hKdvdU : Nat.card ↥K ∣ Nat.card ↥hyp.U := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_U).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcopPK : Nat.Coprime (Nat.card ↥hyp.P) (Nat.card ↥K) :=
    hcop.coprime_dvd_right (hKdvdU.trans hUdvdUW1)
  -- normalizer facts: `S ≤ N(P)`, `U ≤ S`, `W₁ ≤ S`, `W₁ ≤ N(W₂)`.
  have hMFleM : maxNilpotentNormalHall hyp.S ≤ hyp.S :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).mp
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.S)
  have hM'le : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hU_le_S : hyp.U ≤ hyp.S :=
    le_trans (le_trans le_sup_right (le_of_eq hyp.S_deriv_eq_PU.symm)) hM'le
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hW1_le_C : hyp.W1 ≤ Subgroup.centralizer (hyp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    exact (hyp.W1_commutes_W2 x hx z hz).symm
  have hW1_le_N : hyp.W1 ≤ Subgroup.normalizer (hyp.W2 : Set G) :=
    hW1_le_C.trans (Subgroup.centralizer_le_normalizer _)
  have hK_norm_P : K ≤ Subgroup.normalizer (hyp.P : Set G) := (hK_le_U.trans hU_le_S).trans
      hS_norm_P
  -- `U ≤ N(K)` (`U` abelian, `K ≤ U`).
  have hKnormalU : (K.subgroupOf hyp.U).Normal := by
    refine ⟨fun n _ g => ?_⟩
    have hc : g * n * g⁻¹ = n := by rw [mul_comm' g n, mul_inv_cancel_right]
    rw [hc]; assumption
  have hU_norm_K : hyp.U ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hK_le_U
  -- `W₁ ≤ N(K)` (`W₁ ≤ N(U)` and `W₁ ≤ N(N(W₂))`).
  have hW1_norm_K : hyp.W1 ≤ Subgroup.normalizer (K : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]; intro n
    have hwU := Subgroup.mem_normalizer_iff.mp (hyp.W1_normalizes_U hw) n
    have hwN := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hW1_le_N hw)) n
    rw [hK_def, Subgroup.mem_inf, Subgroup.mem_inf, hwU, hwN]
  -- Gorenstein 2.3 decomposition `P = (C(K) ⊓ P) ⊕ ⁅P, K⁆`.
  obtain ⟨hdec_inf, hdec_sup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp hK_norm_P hcopPK
  have hPK_le_P : (⁅hyp.P, K⁆ : Subgroup G) ≤ hyp.P := le_sup_right.trans (le_of_eq hdec_sup)
  -- `W₂ ≤ C(K) ⊓ P`.
  have hW2_le_P : hyp.W2 ≤ hyp.P := W2_le_P hG hyp
  have hW2_le_CK : hyp.W2 ≤ Subgroup.centralizer (K : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]; intro k hk
    exact ((Subgroup.mem_centralizer_iff.mp (hKC hk)) y hy).symm
  -- Wielandt: `U ≤ C(⁅P,K⁆)`.
  have hUEnorm : hyp.U ⊔ hyp.W1 ≤ Subgroup.normalizer ((⁅hyp.P, K⁆ : Subgroup G) : Set G) := by
    rw [sup_le_iff]
    refine ⟨fun u hu => OddOrder.BG.Ch1.S03f.mem_normalizer_commutator ((hU_le_S.trans hS_norm_P)
        hu)
      (hU_norm_K hu), fun w hw => OddOrder.BG.Ch1.S03f.mem_normalizer_commutator
      ((hW1_le_S.trans hS_norm_P) hw) (hW1_norm_K hw)⟩
  have hPKsolv : Group.IsSolvable ↥(⁅hyp.P, K⁆ : Subgroup G) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (by
      have h := hP_elemAb.comm (⟨(a : G), hPK_le_P a.2⟩ : ↥hyp.P) (⟨(b : G), hPK_le_P b.2⟩ : ↥hyp.P)
      have h2 := congrArg (Subgroup.subtype hyp.P) h
      simpa using h2))
  -- `Coprime |⁅P,K⁆| |U⋊W₁|`: `⁅P,K⁆ ≤ P` and `hcop`.
  have hPKdvdP : Nat.card ↥(⁅hyp.P, K⁆ : Subgroup G) ∣ Nat.card ↥hyp.P := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK_le_P).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcopPKfrob : Nat.Coprime (Nat.card ↥(⁅hyp.P, K⁆ : Subgroup G))
      (Nat.card ↥(hyp.U ⊔ hyp.W1)) := hcop.coprime_dvd_left hPKdvdP
  have hUcent : hyp.U ≤ Subgroup.centralizer ((⁅hyp.P, K⁆ : Subgroup G) : Set G) :=
    frobenius_kernel_centralizes_of_complement_fpf hUEnorm data.UW1_frobenius hPKsolv hcopPKfrob
      (by
        intro n hnPK hnfix
        -- `n ∈ ⁅P,K⁆ ⊆ P` fixed by all of `W₁` ⟹ `n ∈ Sdata.W2 = W₂ ⊆ C(K) ⊓ P` ⟹ `n = 1`.
        have hnP : n ∈ hyp.P := hPK_le_P hnPK
        -- a nonidentity `x ∈ W₁ = Sdata.W1`.
        have hW1ne : hyp.Sdata.W1 ≠ ⊥ := hyp.Sdata.W1_nontrivial
        have : Nontrivial ↥hyp.Sdata.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW1ne
        obtain ⟨x0, hx0⟩ := exists_ne (1 : ↥hyp.Sdata.W1)
        have hxW1 : (x0 : G) ∈ hyp.W1 := hyp.Sdata_W1_eq ▸ x0.2
        have hxne : (x0 : G) ≠ 1 := fun h => hx0 (OneMemClass.coe_eq_one.mp h)
        have hnCx : (x0 : G) * n * (x0 : G)⁻¹ = n := hnfix _ hxW1
        have hnCent : n ∈ Subgroup.centralizer ({(x0 : G)} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]; intro z hz
          rw [Set.mem_singleton_iff] at hz; subst hz
          exact (mul_inv_eq_iff_eq_mul.mp hnCx)
        have hnM' : n ∈ derivedInG hyp.S := by
          have hPM' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
          exact hPM' hnP
        have hreg := hyp.Sdata.centralizer_W1 (x0 : G) x0.2 hxne
        have hnW2 : n ∈ hyp.W2 := by
          rw [← hrec, ← hreg]; exact Subgroup.mem_inf.mpr ⟨hnM', hnCent⟩
        have hnInf : n ∈ (Subgroup.centralizer (K : Set G) ⊓ hyp.P) ⊓ (⁅hyp.P, K⁆ : Subgroup G) :=
          Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hW2_le_CK hnW2, hnP⟩, hnPK⟩
        rw [hdec_inf, Subgroup.mem_bot] at hnInf
        exact hnInf)
  -- `⁅P,K⁆ ≤ C(K) ⊓ P`, hence `⁅P,K⁆ = ⊥`.
  have hPK_le_CK : (⁅hyp.P, K⁆ : Subgroup G) ≤ Subgroup.centralizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]; intro k hk
    -- `k ∈ K ≤ U ≤ C(⁅P,K⁆)`, so `k` centralizes `x ∈ ⁅P,K⁆`.
    exact (Subgroup.mem_centralizer_iff.mp (hUcent (hK_le_U hk)) x hx).symm
  have hPK_bot : (⁅hyp.P, K⁆ : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ (Subgroup.centralizer (K : Set G) ⊓ hyp.P) ⊓ (⁅hyp.P, K⁆ : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hPK_le_CK hx, hPK_le_P hx⟩, hx⟩
    rwa [hdec_inf] at this
  -- `⁅P,K⁆ = ⊥ ⟹ K ≤ C(P) ⟹ K ≤ U ⊓ C(P) = ⊥`.
  have hK_le_CP : K ≤ Subgroup.centralizer (hyp.P : Set G) := by
    have hPcentK : hyp.P ≤ Subgroup.centralizer (K : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := hyp.P) (H₂ := K)).mp hPK_bot
    intro k hk
    rw [Subgroup.mem_centralizer_iff]; intro p hp
    exact ((Subgroup.mem_centralizer_iff.mp (hPcentK hp)) k hk).symm
  have : K ≤ hyp.U ⊓ Subgroup.centralizer (hyp.P : Set G) := le_inf hK_le_U hK_le_CP
  rw [U_inf_centralizer_P_eq_bot_of_c_eq_one hyp hc1] at this
  exact le_bot_iff.mp this

end OddOrder.Peterfalvi.S15
