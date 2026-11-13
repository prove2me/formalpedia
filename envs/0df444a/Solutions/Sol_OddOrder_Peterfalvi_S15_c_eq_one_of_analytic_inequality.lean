-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.c_eq_one_of_analytic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:57:25.090214+00:00
-- url     : https://prove2.me/submissions/81f6118f-c28f-4e96-98f6-19b465dcab88

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
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
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
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S15_c_eq_one_forces_params

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

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- Lower estimate for the analytic parameter `m` of **Peterfalvi (13.10)**.
Dropping the (positive) last summand and bounding `(q-1)/q^p ≤ 1/q^2` (valid once
`p ≥ 3`) gives `m ≥ 1 - 1/(q-1) - 1/q^2`. -/
theorem m_value_ge_aux {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (1 : ℚ) - 1 / ((q : ℚ) - 1) - 1 / (q : ℚ) ^ 2 ≤
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hXpos : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hX3 : (q : ℚ) ^ 3 ≤ (q : ℚ) ^ p := pow_le_pow_right₀ (by linarith) hp
  have hfrac : ((q : ℚ) - 1) / (q : ℚ) ^ p ≤ 1 / (q : ℚ) ^ 2 := by
    rw [div_le_div_iff₀ hXpos (by positivity)]
    have e : (q : ℚ) ^ 3 = ((q : ℚ) - 1) * (q : ℚ) ^ 2 + (q : ℚ) ^ 2 := by ring
    have hsq : (0 : ℚ) ≤ (q : ℚ) ^ 2 := sq_nonneg _
    linarith [hX3, e, hsq]
  have hpos : (0 : ℚ) ≤ 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by positivity
  linarith [hfrac, hpos]

/-- **Peterfalvi (13.11.b)** numeric bound: `q ≥ 5 ⇒ m > 7/10`. -/
theorem m_value_gt_seven_tenths {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (7 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have haux := m_value_ge_aux hq hp
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 25 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq5]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11.a)** numeric bound: `q ≥ 7 ⇒ m > 8/10`. -/
theorem m_value_gt_four_fifths {q p : ℕ} (hq : 7 ≤ q) (hp : 3 ≤ p) :
    (8 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : 5 ≤ q := by omega
  have haux := m_value_ge_aux hq5 hp
  have hq7 : (7 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 49 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq7]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11)** numeric core of the `q = 3` branch: once the
Section 16 hypothesis gives `p ≥ 5`, the concrete value of `m` is already
strictly larger than `49/100`. -/
theorem m_value_q_three_gt_49_hundredths {p : ℕ} (hp : 5 ≤ p) :
    (49 : ℚ) / 100 <
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
        1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p) := by
  have h4 : 4 ≤ p - 1 := by omega
  have hpow4 : (3 : ℚ) ^ 4 ≤ (3 : ℚ) ^ (p - 1) :=
    pow_le_pow_right₀ (by norm_num : (0 : ℚ) ≤ 3) h4
  norm_num at hpow4
  have hden_gt : (100 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hden_pos : (0 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hsmall : 1 / (2 * (3 : ℚ) ^ (p - 1)) < (1 : ℚ) / 100 := by
    rw [div_lt_div_iff₀ hden_pos (by norm_num : (0 : ℚ) < 100)]
    nlinarith
  have hpow : (3 : ℚ) ^ p = 3 * (3 : ℚ) ^ (p - 1) := by
    have hp_eq : p = (p - 1) + 1 := by omega
    rw [hp_eq, pow_succ]
    rw [show p - 1 + 1 - 1 = p - 1 by omega]
    ring
  have hexpr :
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
          1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p)
        = (1 : ℚ) / 2 - 1 / (2 * (3 : ℚ) ^ (p - 1)) := by
    rw [hpow]
    field_simp [hden_pos.ne']
    ring
  rw [hexpr]
  linarith [hsmall]

namespace Hypothesis

/-- **Peterfalvi (13.11.a)** at the Section 15 hypothesis level: if `q ≥ 7`,
then the concrete analytic parameter satisfies `m > 8/10`. -/
theorem m_gt_four_fifths_of_seven_le_q (hyp : Hypothesis (G := G))
    (hq7 : 7 ≤ hyp.q) :
    hyp.m > (8 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_four_fifths hq7 hyp.three_le_p

/-- **Peterfalvi (13.11.b)** at the Section 15 hypothesis level: if `q ≥ 5`,
then the concrete analytic parameter satisfies `m > 7/10`. -/
theorem m_gt_seven_tenths_of_five_le_q (hyp : Hypothesis (G := G))
    (hq5 : 5 ≤ hyp.q) :
    hyp.m > (7 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_seven_tenths hq5 hyp.three_le_p

/-- **Peterfalvi (13.11)** at the Section 15 hypothesis level: in the `q = 3`
branch, the `m > 49/100` part follows once an external argument supplies
`p ≥ 5`.  Section 16 supplies this from `q < p`. -/
theorem m_gt_49_hundredths_of_q_eq_three_of_five_le_p
    (hyp : Hypothesis (G := G)) (hq3 : hyp.q = 3) (hp5 : 5 ≤ hyp.p) :
    hyp.m > (49 / 100 : ℚ) := by
  rw [hyp.m_eq, hq3]
  exact m_value_q_three_gt_49_hundredths hp5

end Hypothesis

/-- **Peterfalvi (8.4.d) restricted to `C`**: `W₁` acts fixed-point-freely on `C ⊆ U` by
conjugation — no `w ∈ W₁ #` centralizes any `c ∈ C #`.  `U W₁` is a Frobenius group with kernel `U`
(`typeP_uW1_frobenius`), and `C = U ⊓ C_G(P) ≤ U`, so the Frobenius fpf condition restricts to `C`.
The fpf input to the (13.12) `c ≡ 1 (mod q)` step (Coq `dv_2q_c1`). -/
theorem Hypothesis.W1_fpf_C [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ w ∈ hyp.W1, w ≠ 1 → ∀ c ∈ hyp.C, c ≠ 1 → w * c * w⁻¹ ≠ c := by
  let setup := hyp.toTypesIIIIIIVSetupS hG
  have hUne := setup.nontrivial.1
  change hyp.Sdata.U ≠ ⊥ at hUne
  have frob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hUne
  rw [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at frob
  have hCU : hyp.C ≤ hyp.U := by rw [hyp.C_eq]; exact inf_le_left
  intro w hw hw1 c hc hc1
  have hwL : w ∈ hyp.U ⊔ hyp.W1 := (le_sup_right : hyp.W1 ≤ _) hw
  have hcL : c ∈ hyp.U ⊔ hyp.W1 := (le_sup_left : hyp.U ≤ _) (hCU hc)
  have hne1 : (⟨w, hwL⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h =>
    hw1 (by simpa using congrArg Subtype.val h)
  have hnec : (⟨c, hcL⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h =>
    hc1 (by simpa using congrArg Subtype.val h)
  have hmemw : (⟨w, hwL⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1) :=
    Subgroup.mem_subgroupOf.mpr hw
  have hmemc : (⟨c, hcL⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.U.subgroupOf (hyp.U ⊔ hyp.W1) :=
    Subgroup.mem_subgroupOf.mpr (hCU hc)
  have hconj := frob.conj_frobenius _ hmemw hne1 _ hmemc hnec
  intro heq
  apply hconj
  apply Subtype.ext
  push_cast
  exact heq

/-- `W₁` normalizes `C = U ⊓ C_G(P)`: `W₁ ≤ S ≤ N_G(P)` (so it normalizes `C_G(P)`) and
`W₁ ≤ N_G(U)` (`W1_normalizes_U`), hence it normalizes their intersection.  The `N_G(C)`-input to
the conjugation action of the (13.12) `c ≡ 1 (mod q)` step. -/
theorem Hypothesis.W1_le_normalizer_C (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ Subgroup.normalizer (hyp.C : Set G) := by
  have hW1S : hyp.W1 ≤ hyp.S := by
    have h1 : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    have h2 : hyp.W ≤ hyp.S := by rw [hyp.W_eq_inter]; exact inf_le_left
    exact h1.trans h2
  have hSP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  intro w hw
  have hwP := hSP (hW1S hw)
  have hwU := hyp.W1_normalizes_U hw
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  rw [hyp.C_eq]
  simp only [Subgroup.mem_inf, SetLike.mem_coe]
  -- `w` normalizes `U` and `C_G(P)`; combine.
  have hU_iff : x ∈ hyp.U ↔ w * x * w⁻¹ ∈ hyp.U :=
    Subgroup.mem_set_normalizer_iff.mp hwU x
  have hCP_iff : x ∈ Subgroup.centralizer (hyp.P : Set G) ↔
      w * x * w⁻¹ ∈ Subgroup.centralizer (hyp.P : Set G) := by
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : w⁻¹ * p * w ∈ (hyp.P : Set G) := (Subgroup.mem_set_normalizer_iff''.mp hwP p).mp hp
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) _ hp'
      calc p * (w * x * w⁻¹) = w * ((w⁻¹ * p * w) * x) * w⁻¹ := by group
        _ = w * (x * (w⁻¹ * p * w)) * w⁻¹ := by rw [hcomm]
        _ = (w * x * w⁻¹) * p := by group
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : w * p * w⁻¹ ∈ (hyp.P : Set G) := (Subgroup.mem_set_normalizer_iff.mp hwP p).mp hp
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) _ hp'
      calc p * x = w⁻¹ * ((w * p * w⁻¹) * (w * x * w⁻¹)) * w := by group
        _ = w⁻¹ * ((w * x * w⁻¹) * (w * p * w⁻¹)) * w := by rw [hcomm]
        _ = x * p := by group
  rw [hU_iff, hCP_iff]

/-- **Peterfalvi (13.12), structural step**: `c ≡ 1 (mod q)`.

The cyclic factor `W₁` (order `q`) acts fixed-point-freely on `C ⊆ U` by conjugation
(`W1_fpf_C`, `W1_le_normalizer_C`).  Since `W₁` is a `q`-group, the class equation
(`IsPGroup.card_modEq_card_fixedPoints`) gives `|C| ≡ |C_C(W₁)| (mod q)`, and the fpf condition
makes `C_C(W₁) = {1}`.  This is the Coq `dv_2q_c1` ingredient (`q ∣ c − 1`) of
`FTtypeP_Ind_Fitting_reg_Fcore`. -/
theorem Hypothesis.c_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.c ≡ 1 [MOD hyp.q] := by
  classical
  have : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  have hfpf := hyp.W1_fpf_C hG
  let : MulAction ↥hyp.W1 ↥hyp.C :=
    MulAction.compHom ↥hyp.C (Subgroup.inclusion hyp.W1_le_normalizer_C)
  have hsmul : ∀ (w : ↥hyp.W1) (x : ↥hyp.C), ((w • x : ↥hyp.C) : G) = (w : G) * (x : G) * (w :
      G)⁻¹ :=
    fun _ _ => rfl
  have hW1pg : IsPGroup hyp.q ↥hyp.W1 := IsPGroup.of_card (by rw [← hyp.q_eq_card_W1, pow_one])
  have hmod : Nat.card ↥hyp.C ≡ Nat.card ↥(MulAction.fixedPoints ↥hyp.W1 ↥hyp.C) [MOD hyp.q] :=
    hW1pg.card_modEq_card_fixedPoints ↥hyp.C
  -- `W₁ ≠ ⊥`, pick `w₀ ∈ W₁ #`.
  have hW1ne : hyp.W1 ≠ ⊥ := by
    intro h; have h3 := hyp.three_le_q
    rw [hyp.q_eq_card_W1, h, Subgroup.card_bot] at h3; omega
  have : Nontrivial ↥hyp.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW1ne
  obtain ⟨⟨w₀, hw₀W1⟩, hw₀ne⟩ := exists_ne (1 : ↥hyp.W1)
  have hw₀ne' : w₀ ≠ 1 := by rintro rfl; exact hw₀ne rfl
  -- `C_C(W₁) = {1}`.
  have hfixset : MulAction.fixedPoints ↥hyp.W1 ↥hyp.C = {1} := by
    ext a
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hafix
      by_contra hane
      have hav : (a : G) ≠ 1 := fun h => hane (Subtype.ext h)
      have hc := congrArg (Subtype.val) (hafix ⟨w₀, hw₀W1⟩)
      rw [hsmul] at hc
      exact hfpf w₀ hw₀W1 hw₀ne' (a : G) a.2 hav hc
    · rintro rfl w
      apply Subtype.ext
      rw [hsmul]; simp
  have hfix : Nat.card ↥(MulAction.fixedPoints ↥hyp.W1 ↥hyp.C) = 1 := by
    rw [hfixset]; simp
  rw [hfix, ← hyp.c_eq_card_C] at hmod
  exact hmod

/-- **Peterfalvi (13.12), `dv_2q_c1`**: `2q ∣ c − 1`.  `c ≡ 1 (mod q)` (`c_modEq_one`) and `c` is
odd (`|C| ∣ |G|`, `|G|` odd), so both `q` and `2` divide `c − 1`; coprimality (`q` odd) gives
`2q ∣ c − 1`.  In the `c > 1` branch this forces `c ≥ 2q + 1`, the lower bound Peterfalvi's numeric
elimination contradicts. -/
theorem Hypothesis.two_mul_q_dvd_c_pred [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : 2 * hyp.q ∣ hyp.c - 1 := by
  have hc1 : 1 ≤ hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hq : hyp.q ∣ hyp.c - 1 := (Nat.modEq_iff_dvd' hc1).mp (hyp.c_modEq_one hG).symm
  have hcodd : ¬ 2 ∣ hyp.c := by
    have hcG : hyp.c ∣ Nat.card G := by
      rw [hyp.c_eq_card_C]; exact Subgroup.card_subgroup_dvd_card _
    have hodd : Nat.card G % 2 = 1 := Nat.odd_iff.mp hG.odd
    intro h2c
    have h2G : (2 : ℕ) ∣ Nat.card G := h2c.trans hcG
    omega
  have h2 : 2 ∣ hyp.c - 1 := by omega
  have hcop : Nat.Coprime 2 hyp.q :=
    (Nat.coprime_primes Nat.prime_two hyp.q_prime).mpr (Ne.symm hyp.q_ne_two)
  exact hcop.mul_dvd_of_dvd_of_dvd h2 hq

/-- **Peterfalvi (13.12), the isolated `PC`-Hall obligation**: for the numerically-forced
`p = 5, q = 3, c = 7`, the subgroup `PC = P ⊔ C` is contained in `M_F = maxNilpotentNormalHall S`.

Peterfalvi's argument: `PC` is **abelian** (hence nilpotent) — `P` is elementary abelian, `C ≤ U` is
abelian, and `C` centralizes `P` (`C_eq`); it is **normal** in `S` (type-`P` `W₁`-structure); and it
is a **Hall** subgroup once `gcd(c, u) = 1`, which holds because case (9.7.b) for `S`
(as `p − 1 = 4`
has no odd divisor `≠ 1`) forces `u ∣ (p^q − 1)/(p − 1) = 31` (Singer / `typeP_Galois`), coprime to
`c = 7`.

The Lean proof follows the same dichotomy.  In Clifford case (a), `a ∣ p − 1 = 4` and oddness of
`a` force `a = 1`; the resulting trivial action on the orbit generator `S₀` contradicts
`caseA_fixed_contradiction`.  In case (b), `CliffordCaseBData.u_dvd_norm_quotient` gives
`u ∣ 31`.  The already-proved normality and commutativity of `H = PC`, together with its card/index
formulas, then give the normal nilpotent Hall subgroup absorbed by `le_maxNilpotentNormalHall`. -/
theorem pc_le_maxNilpotentNormalHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hp5 : hyp.p = 5) (hq3 : hyp.q = 3) (hc7 : hyp.c = 7) :
    hyp.P ⊔ hyp.C ≤ maxNilpotentNormalHall hyp.S :=
  by
  have := hyp.finiteG
  change hyp.H ≤ maxNilpotentNormalHall hyp.S
  -- The (9.7) dichotomy: case (a) is impossible for `p - 1 = 4`; case (b) gives `u ∣ 31`.
  have hu_dvd_31 : hyp.u ∣ 31 := by
    obtain ⟨chief, -⟩ :=
      OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
    rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
        (hyp.mkSection11CharacterDataS hG chief) with hA | hB
    · obtain ⟨caseA⟩ := hA
      exfalso
      have ha_dvd_4 : caseA.a ∣ 4 := by
        have h := caseA.a_dvd_p_sub_one
        rw [hyp.chiefFactorS_p_eq hG chief, hp5] at h
        norm_num at h ⊢
        exact h
      have ha_cop_4 : Nat.Coprime caseA.a 4 := by
        have h := (Nat.coprime_two_left.mpr
          (OddOrder.Peterfalvi.S11.caseA_a_odd hG caseA)).symm.pow_right 2
        norm_num at h ⊢
        exact h
      have ha_one : caseA.a = 1 :=
        Nat.eq_one_of_dvd_coprimes ha_cop_4 dvd_rfl ha_dvd_4
      have hrange_card : Nat.card
          ↥(OddOrder.Peterfalvi.S11.aInvariantRestrictAut caseA.S0_aInvariant).range = 1 := by
        rw [← caseA.a_eq_card_restrictAut_range, ha_one]
      have hrange_bot :
          (OddOrder.Peterfalvi.S11.aInvariantRestrictAut caseA.S0_aInvariant).range = ⊥ :=
        Subgroup.card_eq_one.mp hrange_card
      let j0 : Fin (hyp.toTypesIIIIIIVSetupS hG).q :=
        ⟨0, (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos⟩
      have hS0card : Nat.card ↥caseA.S0 = chief.p := by
        have h := caseA.Hpart_order j0
        rwa [caseA.Hpart_orbit j0, card_pointwise_smul] at h
      have hS0ne : caseA.S0 ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hS0card
        exact chief.p_prime.one_lt.ne' hS0card.symm
      refine OddOrder.Peterfalvi.S13.caseA_fixed_contradiction chief hS0ne ?_
      intro v s hs
      have hvRange :
          OddOrder.Peterfalvi.S11.aInvariantRestrictAut caseA.S0_aInvariant v ∈
            (OddOrder.Peterfalvi.S11.aInvariantRestrictAut caseA.S0_aInvariant).range :=
        ⟨v, rfl⟩
      rw [hrange_bot, Subgroup.mem_bot] at hvRange
      have happ := congrArg
        (fun f : MulAut ↥caseA.S0 => f ⟨s, hs⟩) hvRange
      have hval := congrArg Subtype.val happ
      change (OddOrder.Peterfalvi.S11.uActionHom (hyp.toTypesIIIIIIVSetupS hG) chief) v s = s
      exact hval
    · obtain ⟨caseB⟩ := hB
      have h := caseB.u_dvd_norm_quotient
      rw [hyp.mkSection11CharacterDataS_u_eq hG chief,
        hyp.chiefFactorS_p_eq hG chief, hyp.toTypesIIIIIIVSetupS_q_eq hG, hp5, hq3] at h
      norm_num at h ⊢
      exact h
  -- `|H| = 5^3·7` and `[S:H] = 3u`, with `u ∣ 31`, are coprime.
  have hcop_u : Nat.Coprime (5 ^ 3 * 7) hyp.u :=
    (show Nat.Coprime (5 ^ 3 * 7) 31 by norm_num).coprime_dvd_right hu_dvd_31
  have hcop_three : Nat.Coprime (5 ^ 3 * 7) 3 := by norm_num
  have hHcop : Nat.Coprime (Nat.card ↥hyp.H) ((hyp.H.subgroupOf hyp.S).index) := by
    rw [hyp.card_H_eq hG, hyp.H_index_eq_uq hG, hp5, hq3, hc7]
    exact Nat.Coprime.mul_right hcop_u hcop_three
  have hHhall := OddOrder.BG.Ch4.S15.isHallSubgroup_primeFactors_of_coprime_index
    hyp.H_le_S hHcop
  have hHcomm : IsMulCommutative ↥(hyp.H.subgroupOf hyp.S) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hyp.H_le_S).symm (hyp.H_mulCommutative hG)
  have hHnil : Group.IsNilpotent ↥(hyp.H.subgroupOf hyp.S) := inferInstance
  exact OddOrder.BG.Ch4.S15.le_maxNilpotentNormalHall hyp.H_le_S
    (H_sharp_subgroupOf_normal hyp) hHnil hHhall

/-- **Peterfalvi (13.12), structural residual**: the numerically-forced case
`p = 5, q = 3, c = 7` is impossible.  By `pc_le_maxNilpotentNormalHall`,
`PC = P ⊔ C ≤ M_F = P` (`P_eq_SF`), so `C ≤ P`; but `|C| = c = 7` cannot divide
`|P| = p^q = 125`.  The preceding theorem discharges the Clifford/Singer Hall obligation;
the remaining `C ≤ P ⟹ 7 ∣ 125` maximality contradiction is discharged here. -/
theorem c_eq_one_final_case [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hp5 : hyp.p = 5) (hq3 : hyp.q = 3) (hc7 : hyp.c = 7) : False := by
  -- `C ≤ P ⊔ C ≤ M_F = P`.
  have hCleP : hyp.C ≤ hyp.P := by
    have h := pc_le_maxNilpotentNormalHall hG hyp hp5 hq3 hc7
    rw [← hyp.P_eq_SF] at h
    exact le_trans le_sup_right h
  -- `|C| = 7`, `|P| = p^q = 125`.
  have hCcard : Nat.card ↥hyp.C = 7 := by rw [← hyp.c_eq_card_C, hc7]
  have hPcard : Nat.card ↥hyp.P = 5 ^ 3 := by
    obtain ⟨_, _, _, hcard, _, _⟩ := basic_structure hG hyp
    rw [hcard, hp5, hq3]
  -- `C ≤ P ⟹ |C| ∣ |P|`, i.e. `7 ∣ 125`, false.
  have hdvd : Nat.card ↥hyp.C ∣ Nat.card ↥hyp.P := by
    have hd := Subgroup.card_subgroup_dvd_card (hyp.C.subgroupOf hyp.P)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleP).toEquiv] at hd
  rw [hCcard, hPcard] at hdvd
  norm_num at hdvd

/-- **The analytic core of Peterfalvi (13.12)** (side-agnostic, pure `ℚ`-arithmetic).

From the `(13.10)` analytic inequality `u/c > m·a^(b−1)/b` and the `(13.2.c)` Singer *upper*
bound `u·(a−1) ≤ a^b − 1`, derive the upper bound `m < b·(a^b−1) / (c·a^(b−1)·(a−1))` that
(with the fixed-point-free lower bound `c ≥ 2b+1`) feeds the finite numeric elimination.

Both the `S`-side `c = 1` finish (`c_eq_one`, `a = p, b = q, u = u, c = c`) and the `T`-side
`d = 1` dual (`a = q, b = p, u = v, c = d`) instantiate this same core; extracted per issue
9013 (案A: generalize the §13 estimate so both sides `cite` it).  Uses only the Singer *upper*
bound, so it is ungated (the `T`-side lower-bound gate of the (13.15) `v`-value is a different
consumer — the ratio inequality — and does not enter here). -/
theorem analytic_singer_m_bound {a b u c : ℕ} {m : ℚ}
    (hbR : (0 : ℚ) < b) (hcR : (0 : ℚ) < c) (haR : (1 : ℚ) < a)
    (hanalytic : (u : ℚ) / c > m * (a : ℚ) ^ (b - 1) / b)
    (hsinger : (u : ℚ) * ((a : ℚ) - 1) ≤ (a : ℚ) ^ b - 1) :
    m < (b : ℚ) * ((a : ℚ) ^ b - 1)
      / ((c : ℚ) * (a : ℚ) ^ (b - 1) * ((a : ℚ) - 1)) := by
  have haR0 : (0 : ℚ) < (a : ℚ) := by linarith
  have hp1R : (0 : ℚ) < (a : ℚ) - 1 := by linarith
  -- From (13.10): `m · a^(b-1) · c < u · b`.
  rw [gt_iff_lt, div_lt_div_iff₀ hbR hcR] at hanalytic
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right hanalytic hp1R,
    mul_le_mul_of_nonneg_left hsinger (le_of_lt hbR)]

/-- **Peterfalvi (13.12)**: the centralizer parameter `c` is `1`.

The numeric elimination `c_eq_one_forces_params` — fed the (13.10) analytic inequality
(`analytic_inequality`, `u/c > m p^(q-1)/q`), the (13.2.c) Singer bound (`basic_structure`,
`u ≤ (p^q-1)/(p-1)`), the fixed-point-free lower bound `c ≥ 2q+1` (`two_mul_q_dvd_c_pred`), and the
(13.11) `m`-bounds — forces `p = 5, q = 3, c = 7`, ruled out by the isolated structural residual
`c_eq_one_final_case`. -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ)) :
    hyp.c = 1 := by
  by_contra hne
  -- `c > 1`; with `2q ∣ c − 1` (`two_mul_q_dvd_c_pred`) this forces `c ≥ 2q + 1`.
  have hc1 : 1 ≤ hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hcgt : 1 < hyp.c := lt_of_le_of_ne hc1 (Ne.symm hne)
  have hc_ge : 2 * hyp.q + 1 ≤ hyp.c := by
    have h2q : 2 * hyp.q ≤ hyp.c - 1 := Nat.le_of_dvd (by omega) (hyp.two_mul_q_dvd_c_pred hG)
    omega
  -- (13.10) analytic inequality: `u/c > m · p^(q-1) / q`.
  have hWcast : ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) = (hyp.p : ℚ) ^ (hyp.q - 1) := by push_cast; ring
  rw [hWcast] at h1310
  -- (13.2.c) Singer bound: `u ≤ (p^q - 1)/(p - 1)`, hence `u · (p-1) ≤ p^q - 1`.
  obtain ⟨_, _, _, _, hu_bound, _⟩ := basic_structure hG hyp
  have hp1nat : 1 ≤ hyp.p := hyp.p_prime.one_le
  have hp0nat : 0 < hyp.p - 1 := by have := hyp.three_le_p; omega
  have hpq1 : 1 ≤ hyp.p ^ hyp.q := Nat.one_le_pow _ _ hyp.p_prime.pos
  have huP : hyp.u * (hyp.p - 1) ≤ hyp.p ^ hyp.q - 1 :=
    (Nat.le_div_iff_mul_le hp0nat).mp hu_bound
  have huPR : (hyp.u : ℚ) * ((hyp.p : ℚ) - 1) ≤ (hyp.p : ℚ) ^ hyp.q - 1 := by
    have h1 : ((hyp.u * (hyp.p - 1) : ℕ) : ℚ) ≤ ((hyp.p ^ hyp.q - 1 : ℕ) : ℚ) := by
      exact_mod_cast huP
    have e1 : ((hyp.u * (hyp.p - 1) : ℕ) : ℚ) = (hyp.u : ℚ) * ((hyp.p : ℚ) - 1) := by
      push_cast [Nat.cast_sub hp1nat]; ring
    have e2 : ((hyp.p ^ hyp.q - 1 : ℕ) : ℚ) = (hyp.p : ℚ) ^ hyp.q - 1 := by
      push_cast [Nat.cast_sub hpq1]; ring
    rw [e1, e2] at h1; exact h1
  -- Positivity, then the side-agnostic analytic core (`analytic_singer_m_bound`) assembles the
  -- abstract bound `m < q(p^q-1)/(c p^(q-1)(p-1))` from (13.10) + the Singer bound.
  have hqR : (0 : ℚ) < (hyp.q : ℚ) := by exact_mod_cast hyp.q_prime.pos
  have hcRpos : (0 : ℚ) < (hyp.c : ℚ) := by exact_mod_cast (show 0 < hyp.c by omega)
  have haR : (1 : ℚ) < (hyp.p : ℚ) := by
    have : (3 : ℚ) ≤ (hyp.p : ℚ) := by exact_mod_cast hyp.three_le_p
    linarith
  have hbound := analytic_singer_m_bound hqR hcRpos haR h1310 huPR
  -- Numeric elimination forces `p = 5, q = 3, c = 7`.
  obtain ⟨hp5, hq3, hc7⟩ := c_eq_one_forces_params hyp.p_prime hyp.q_prime hyp.three_le_p
    hyp.q_ne_two hyp.p_ne_q hc_ge (hyp.two_mul_q_dvd_c_pred hG)
    (fun h => hyp.m_gt_seven_tenths_of_five_le_q h)
    (fun h => hyp.m_gt_four_fifths_of_seven_le_q h)
    (fun hq hp => hyp.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq hp)
    hyp.m_eq hbound
  exact c_eq_one_final_case hG hyp hp5 hq3 hc7

end OddOrder.Peterfalvi.S15
