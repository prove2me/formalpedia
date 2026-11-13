-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.lambda_forces_T_caseB_core
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:08:39.819581+00:00
-- url     : https://prove2.me/submissions/91010a2d-1d38-4d1f-97f6-a07e0f5d136a

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
import Theorems.Thm_OddOrder_Peterfalvi_S15_tSide_theta_package_of_not_caseB_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_P_conj_forall_not_le_T
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S15_eta_cross_expansion_ne_zero

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

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Peterfalvi (13.4), Core/λ-cluster form** (the core/lam restatement of
`lambda_forces_T_caseB`, issue 9094 案 A): if `𝒮` contains the λ-cluster (a degree-`uq`
character induced from a linear character of `PC`), then case (9.7.b) holds for `T`, with
`D = 1`, `v = (q^p−1)/(q−1)` and `|Q| = q^p`.  The witnesses of the Core `mu_col` field and
the λ-cluster thread the guarded `tau1S_apply_induce_sub`/`tau1S_induce_inner_eta`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (pins : NuGridSupplyData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  have := hyp.finiteG
  by_contra hne
  -- T-side θ-package from the (13.3.b,c)-for-`T` gate.
  obtain ⟨θT, r, r', δ', θG, hδ', hβsupp, hβform, hηθ, hLamTheta⟩ :=
    tSide_theta_package_of_not_caseB_core hG core lam pins hne
  -- S-side (13.3) data with the `𝒮₁`-witnesses.
  obtain ⟨thetaL, hthetaLirr, hthetaL1, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  have hthetaLP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel thetaL) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  obtain ⟨j₀, δ, θlin, -, hδ, hθlinirr, hθlin1, hθlinP, hμeq, hμtau⟩ :=
    core.mu_col_tau1_eta_col_one
  -- `α = λ − μ_{j₀}` is supported on `H^#` (`H ⊴ S`; both terms `H`-induced of equal degree).
  have hKnorm : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
  have hαsupp : (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀).support ⊆
      {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1} := by
    intro s hs
    have hs0 : (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀) s ≠ 0 := hs
    refine ⟨?_, ?_⟩
    · by_contra hsH
      apply hs0
      have hsH' : s ∉ hyp.H.subgroupOf hyp.S := fun h => hsH (Subgroup.mem_subgroupOf.mp h)
      rw [ClassFunction.sub_apply, hlamEq, hμeq,
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH',
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH', sub_zero]
    · rintro rfl
      apply hs0
      rw [ClassFunction.sub_apply, hlamEq, hμeq, ClassFunction.induce_apply_one,
        ClassFunction.induce_apply_one, hthetaL1, hθlin1, sub_self]
  -- The conjugate closures of `H^#` and `K^#` are disjoint.
  have hdisj := disjoint_conjugatesIntoSet_of_centralizer
    (A_M := {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1})
    (A_N := {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1})
    (fun _y hy => hyp.P_le_centralizer_of_mem_H hG hy.1)
    (fun z hz => QD_sharp_centralizer_le_T hG hyp z hz.1 hz.2)
    (P_conj_forall_not_le_T hG hyp)
  -- Hence `(α^τ, β^τ) = 0`.
  have h0 : ClassFunction.inner
      (ClassFunction.induce hyp.S (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀))
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)) = 0 :=
    inner_induce_induce_eq_zero_of_disjoint hαsupp hβsupp hdisj
  -- Rewrite `α^τ = λ° − δ·∑ᵢ η_{i1}` ((13.2.e)+τ₁-additivity + the (13.3.c) column formula).
  have hαform : ClassFunction.induce hyp.S (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀)
      = core.tau1S lam.lambda
        - (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ := by
    conv_lhs => rw [hlamEq, hμeq]
    rw [← core.tau1S_apply_induce_sub thetaL θlin hthetaLirr hθlinirr hthetaLP hθlinP,
      map_sub, ← hlamEq, ← hμeq, hμtau]
  -- The `λ°`-side grid orthogonality, flipped to the expansion brick's slot order.
  have hLamEta : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (core.tau1S lam.lambda) (hyp.eta i j) = 0 := by
    intro i j
    have h := core.tau1S_induce_inner_eta i j thetaL hthetaLirr hthetaLP
      (hlamEq ▸ lam.lambda_irreducible)
    rw [← hlamEq] at h
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  -- The bilinear expansion is `δ·δ' ≠ 0` — contradiction.
  rw [hαform, hβform] at h0
  exact eta_cross_expansion_ne_zero hyp.eta (fun i k j l => hyp.eta_orthonormal i k j l)
    (core.tau1S lam.lambda) θG r' ⟨1, hyp.p_prime.one_lt⟩ hLamEta hηθ hLamTheta hδ hδ' h0

end OddOrder.Peterfalvi.S15
