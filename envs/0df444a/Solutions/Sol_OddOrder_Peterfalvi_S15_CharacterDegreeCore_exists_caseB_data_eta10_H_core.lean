-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.CharacterDegreeCore.exists_caseB_data_eta10_H_core
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:03:18.236205+00:00
-- url     : https://prove2.me/submissions/8e829f7b-9422-44ea-a115-8aeae1aa501a

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Algebra/GaloisRationalInteger.lean
--   OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Canonicalization.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/HSharpChosenBase.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10HCorrection.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
import Theorems.Thm_OddOrder_Peterfalvi_S15_H_sharp_hypothesis76_base_cCoeff_int
import Theorems.Thm_OddOrder_Peterfalvi_S15_H_sharp_hypothesis76_base_alphaFun_inflation
import Theorems.Thm_OddOrder_Peterfalvi_S15_eta10_cCoeff_base_eq_zero
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_eta10_apply_sub_one_integral
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient

-- ===== OddOrder/Algebra/GaloisRationalInteger.lean =====
namespace OddOrder.Algebra

open Polynomial IntermediateField

open OddOrder.RepresentationTheory in
/-- **Virtual characters have integer degree**: `φ(1) ∈ ℤ` for `φ ∈ ℤ[Irr G]` — irreducible
characters have `χ(1) = dim ∈ ℕ` (`Representation.char_one`), and the value at `1` is
`ℤ`-linear in `φ`. -/
theorem exists_int_apply_one_of_mem_ZIrr {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    ∃ z : ℤ, φ 1 = (z : ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, hchar⟩ := IsIrreducibleCharacter.isCharacter hx
      refine ⟨Module.finrank ℂ V, ?_⟩
      rw [show x 1 = ρ.character 1 from congrFun hchar 1, Representation.char_one]
      push_cast
      ring
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
      obtain ⟨za, hza⟩ := ha
      obtain ⟨zb, hzb⟩ := hb
      refine ⟨za + zb, ?_⟩
      rw [ClassFunction.add_apply, hza, hzb]
      push_cast
      ring
  | smul n a _ ha =>
      obtain ⟨za, hza⟩ := ha
      refine ⟨n * za, ?_⟩
      rw [ClassFunction.zsmul_apply, hza, zsmul_eq_mul]
      push_cast
      ring

end OddOrder.Algebra

-- ===== OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean =====
namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]

variable {k : Type*} [CommRing k]

variable [Fintype G] [Invertible (Nat.card H : k)]

section Complex

variable [Fintype H] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]

open scoped Classical in
omit [Fintype ↥H] in
omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)] in
/-- **The conjugate-orbit sum is a virtual character**: each summand of the orbit
`{θ^{x⁻¹} : x ∈ G}` is (the coercion of) an irreducible character of `H`
(`IrreducibleCharacter.conjBy`), so the sum lies in `ℤ[Irr H]`.  Together with
`card_smul_restrict_induce_eq_inertia_smul_orbitSum` this makes
`(1/‖Ind θ‖²)·Res_H(Ind θ)` a genuine (ℕ-combination) character — the integrality carrier of
Peterfalvi (13.5.a). -/
theorem orbitSum_mem_ZIrr [Finite H] (θ : IrreducibleCharacter H) :
    (∑ ψ ∈ Finset.univ.image
        (fun x : G => ClassFunction.conjBy x⁻¹ (θ : ClassFunction ↥H ℂ)), ψ) ∈ ZIrr ↥H := by
  refine Submodule.sum_mem _ (fun ψ hψ => ?_)
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hψ
  rw [← IrreducibleCharacter.coe_conjBy]
  exact (IrreducibleCharacter.conjBy x⁻¹ θ).2.mem_ZIrr

end Complex

end OddOrder.RepresentationTheory

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

/-- **The self inner product of a virtual character is a natural number**: `⟨φ,φ⟩ ∈ ℤ`
(`inner_mem_ZIrr_int`) and `|H|·⟨φ,φ⟩ = ∑‖φ‖² ≥ 0` (`sum_normSq_eq_card_mul_inner`), so the
integer is nonnegative.  The `n = ‖α‖²` of the (13.7) Parseval bookkeeping. -/
theorem exists_nat_inner_self_of_mem_ZIrr {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] {φ : ClassFunction H ℂ}
    (hφ : φ ∈ OddOrder.RepresentationTheory.ZIrr H) :
    ∃ n : ℕ, ClassFunction.inner φ φ = (n : ℂ) := by
  obtain ⟨z, hz⟩ := ClassFunction.inner_mem_ZIrr_int hφ hφ
  have hsum := sum_normSq_eq_card_mul_inner φ
  rw [hz] at hsum
  have hcard : (0 : ℝ) < (Nat.card H : ℝ) := by exact_mod_cast Nat.card_pos
  have hzr : ((Nat.card H : ℝ) * (z : ℝ) : ℂ) = ((∑ g : H, ‖φ g‖ ^ 2 : ℝ) : ℂ) := by
    rw [hsum]
    push_cast
    ring
  have hzreal : (Nat.card H : ℝ) * (z : ℝ) = ∑ g : H, ‖φ g‖ ^ 2 := by exact_mod_cast hzr
  have hz0 : (0 : ℤ) ≤ z := by
    by_contra hneg
    push Not at hneg
    have h1 : (z : ℝ) < 0 := by exact_mod_cast hneg
    have h2 : (Nat.card H : ℝ) * (z : ℝ) < 0 := mul_neg_of_pos_of_neg hcard h1
    have h3 : (0 : ℝ) ≤ ∑ g : H, ‖φ g‖ ^ 2 :=
      Finset.sum_nonneg (fun g _ => by positivity)
    linarith [hzreal ▸ h2]
  refine ⟨z.toNat, ?_⟩
  rw [hz]
  have := Int.toNat_of_nonneg hz0
  exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) this.symm

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
/-- Generic (13.5.a) point formula, `a = 0` form: if every `P'`-non-kernel coefficient of `χ`
vanishes, then on `A` the character `χ` is its `P'`-kernel tail. -/
theorem hypothesis76_point_formula_kernel_only [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (hHbot : ∀ a : {a : G // a ∈ A}, H76.hyp71.hyp.H a = ⊥)
    (P' : Subgroup ↥L) (χ : ClassFunction G ℂ)
    (hall : ∀ i : Fin (H76.n + 1), 0 < i →
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) →
      H76.cCoeff χ i = 0)
    (a : ↥L) (ha : (a : G) ∈ A) :
    χ (a : G) =
      ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
            (fun i => (P' : Set ↥L) ⊆
              OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a := by
  classical
  have hbase : χ (a : G) = ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a :=
    (chiRho_eq_self_of_H_eq_bot H76.hyp71 hHbot χ a ha).symm.trans
      (OddOrder.Peterfalvi.S09.Hypothesis76.chiRho_explicit_formula H76 χ ha)
  rw [hbase, ← Finset.sum_filter_add_sum_filter_not (Finset.Ioi 0)
    (fun i => (P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))]
  have hmid0 : ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter (fun i =>
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter] at hi
    rw [hall i (Finset.mem_Ioi.mp hi.1) hi.2, star_zero, zero_div, zero_mul]
  rw [hmid0, add_zero]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The generic correction is constant on `P'`. -/
theorem hypothesis76AlphaFun_const [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) :
    ∀ x ∈ P', hypothesis76AlphaFun H76 P' χ x = hypothesis76AlphaFun H76 P' χ 1 := by
  classical
  intro x hx
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hker := (Finset.mem_filter.mp hi).2
  rw [show H76.zeta i x = H76.zeta i 1 from hker hx]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- For an abstract (7.6) datum, restriction of a family member to its inducing normal
subgroup is its squared norm times the orbit sum of an inducing irreducible character. -/
theorem hypothesis76_restrict_zeta_eq_orbitSum [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (j : Fin (H76.n + 1)) :
    ∃ θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(H76.H.subgroupOf L),
      H76.zeta j = ClassFunction.induce (H76.H.subgroupOf L)
          (θ : ClassFunction ↥(H76.H.subgroupOf L) ℂ) ∧
      (haveI : (H76.H.subgroupOf L).Normal :=
        OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
      ClassFunction.restrict (H76.H.subgroupOf L) (H76.zeta j)
        = H76.zetaNormSq j •
            ∑ ψ ∈ Finset.univ.image (fun x : ↥L =>
              ClassFunction.conjBy x⁻¹
                (θ : ClassFunction ↥(H76.H.subgroupOf L) ℂ)), ψ) := by
  classical
  set K : Subgroup ↥L := H76.H.subgroupOf L with hKdef
  have hKnorm : K.Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
  obtain ⟨θ₀, hθ₀⟩ := H76.zeta_induced j
  have hθ : H76.zeta j = ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) := by
    rw [hθ₀]
  refine ⟨θ₀, hθ, ?_⟩
  have hK0 : (Nat.card ↥K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have horbit := OddOrder.RepresentationTheory.card_smul_restrict_induce_eq_inertia_smul_orbitSum
    (G := ↥L) (H := K) (k := ℂ) (θ₀ : ClassFunction ↥K ℂ)
  have hinertia := OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
    (G := ↥L) (H := K) θ₀
  have hnormval : (Nat.card ↥K : ℂ) * H76.zetaNormSq j
      = (Nat.card ↥(ClassFunction.inertia (G := ↥L)
          (θ₀ : ClassFunction ↥K ℂ)) : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hθ]
    exact hinertia
  have hIKnorm : ((Nat.card ↥K : ℂ))⁻¹ *
      (Nat.card ↥(ClassFunction.inertia (G := ↥L)
        (θ₀ : ClassFunction ↥K ℂ)) : ℂ) = H76.zetaNormSq j := by
    rw [← hnormval]
    field_simp
  have h1 : (Nat.card ↥K : ℂ) • ClassFunction.restrict K (H76.zeta j)
      = ((Nat.card ↥(ClassFunction.inertia (G := ↥L)
          (θ₀ : ClassFunction ↥K ℂ)) : ℕ) : ℂ) •
          ∑ ψ ∈ Finset.univ.image
            (fun x : ↥L => ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ)] at horbit
    rw [hθ]
    exact horbit
  have h2 := congrArg (fun φ => ((Nat.card ↥K : ℂ))⁻¹ • φ) h1
  simp only [smul_smul, inv_mul_cancel₀ hK0, one_smul] at h2
  rw [h2, hIKnorm]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The normalized restriction `Res ζ_i / ‖ζ_i‖²` of an abstract (7.6) family member is a
virtual character: it is the orbit sum of the inducing irreducible character. -/
theorem hypothesis76_inv_normSq_restrict_zeta_mem_ZIrr [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (i : Fin (H76.n + 1)) :
    (H76.zetaNormSq i)⁻¹ •
        ClassFunction.restrict (H76.H.subgroupOf L) (H76.zeta i)
      ∈ ZIrr ↥(H76.H.subgroupOf L) := by
  classical
  set K : Subgroup ↥L := H76.H.subgroupOf L with hKdef
  have hKnorm : K.Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
  obtain ⟨θ₀, hθ₀⟩ := H76.zeta_induced i
  have hθ : H76.zeta i = ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) := by
    rw [hθ₀]
  have hinertia := OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
    (G := ↥L) (H := K) θ₀
  have hnormval : (Nat.card ↥K : ℂ) * H76.zetaNormSq i
      = (Nat.card ↥(ClassFunction.inertia (G := ↥L)
          (θ₀ : ClassFunction ↥K ℂ)) : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hθ]
    exact hinertia
  have hI0 : (Nat.card ↥(ClassFunction.inertia (G := ↥L)
      (θ₀ : ClassFunction ↥K ℂ)) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hnorm0 : H76.zetaNormSq i ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnormval
    exact hI0 hnormval.symm
  obtain ⟨θ, -, hres⟩ := hypothesis76_restrict_zeta_eq_orbitSum H76 i
  have hmain : (H76.zetaNormSq i)⁻¹ •
      ClassFunction.restrict K (H76.zeta i)
      = ∑ ψ ∈ Finset.univ.image (fun x : ↥L =>
          ClassFunction.conjBy x⁻¹ (θ : ClassFunction ↥K ℂ)), ψ := by
    rw [hres, smul_smul, inv_mul_cancel₀ hnorm0, one_smul]
  rw [hmain]
  exact OddOrder.RepresentationTheory.orbitSum_mem_ZIrr (G := ↥L) θ

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- If the (7.7.a) coefficients are integral, the generic `P'`-kernel correction restricts
to a virtual character of `H76.H`. -/
theorem hypothesis76AlphaCF_restrict_mem_ZIrr [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ)
    (hc : ∀ i, ∃ z : ℤ, H76.cCoeff χ i = (z : ℂ)) :
    ClassFunction.restrict (H76.H.subgroupOf L) (hypothesis76AlphaCF H76 P' χ)
      ∈ ZIrr ↥(H76.H.subgroupOf L) := by
  classical
  set K : Subgroup ↥L := H76.H.subgroupOf L with hKdef
  have hlin : ClassFunction.restrict K (hypothesis76AlphaCF H76 P' χ)
      = ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
            (fun i => (P' : Set ↥L) ⊆
              OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) •
            ClassFunction.restrict K (H76.zeta i) := by
    ext x
    rw [ClassFunction.restrict_apply, hypothesis76AlphaCF,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [ClassFunction.smul_apply, ClassFunction.smul_apply, ClassFunction.restrict_apply])
  rw [hlin]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  obtain ⟨z, hz⟩ := hc i
  rw [hz, star_intCast, div_eq_mul_inv, mul_smul, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ z (hypothesis76_inv_normSq_restrict_zeta_mem_ZIrr H76 i)

end GenericAlpha

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

open scoped Classical in
/-- **Sharp-set Parseval bookkeeping** (the `s + d² = |H|·n` shape of Peterfalvi (13.7)): for a
function `f` agreeing on `K` with a class function `ψ` of self inner product `n`, the
squared-norm sum over the nonidentity `K`-members is `|K|·n − ‖f(1)‖²`. -/
theorem sum_filter_erase_one_normSq_eq {L : Type*} [Group L] [Fintype L]
    {K : Subgroup L} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (f : L → ℂ) (ψ : ClassFunction ↥K ℂ) (hagree : ∀ k : ↥K, f ↑k = ψ k)
    {n : ℕ} (hn : ClassFunction.inner ψ ψ = (n : ℂ)) :
    ∑ x ∈ (Finset.univ.filter (· ∈ K)).erase 1, ‖f x‖ ^ 2
      = (Nat.card ↥K : ℝ) * (n : ℝ) - ‖f 1‖ ^ 2 := by
  classical
  -- The full `K`-sum is `|K|·n` (Parseval on `↥K`).
  have htotal : ∑ x ∈ Finset.univ.filter (· ∈ K), ‖f x‖ ^ 2
      = (Nat.card ↥K : ℝ) * (n : ℝ) := by
    have hbij : ∑ x ∈ Finset.univ.filter (· ∈ K), ‖f x‖ ^ 2 = ∑ k : ↥K, ‖ψ k‖ ^ 2 := by
      refine Finset.sum_bij' (fun x hx => (⟨x, (Finset.mem_filter.mp hx).2⟩ : ↥K))
        (fun k _ => (k : L)) ?_ ?_ ?_ ?_ ?_
      · intro x hx; exact Finset.mem_univ _
      · intro k _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.2⟩
      · intro x hx; rfl
      · intro k _; rfl
      · intro x hx
        rw [hagree ⟨x, (Finset.mem_filter.mp hx).2⟩]
    have hpars : ((∑ k : ↥K, ‖ψ k‖ ^ 2 : ℝ) : ℂ) = (Nat.card ↥K : ℂ) * (n : ℂ) := by
      rw [sum_normSq_eq_card_mul_inner, hn]
    have hpars' : ∑ k : ↥K, ‖ψ k‖ ^ 2 = (Nat.card ↥K : ℝ) * (n : ℝ) := by
      exact_mod_cast hpars
    rw [hbij, hpars']
  have h1mem : (1 : L) ∈ Finset.univ.filter (· ∈ K) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, K.one_mem⟩
  have hsplit : ∑ x ∈ (Finset.univ.filter (· ∈ K)).erase 1, ‖f x‖ ^ 2
      = (∑ x ∈ Finset.univ.filter (· ∈ K), ‖f x‖ ^ 2) - ‖f 1‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ h1mem]
    ring
  rw [hsplit, htotal]

open scoped FiniteInduce in
/-- **`η₁₀` is a virtual character of `G`** — real content of the 3002-threaded grid:
`η₁₀ = τ₃(ω₁₀)` (`eta_eq_tau_omega`), `ω₁₀ ∈ ZIrr W` (`omega_mem_ZIrr`), and `τ₃` preserves
virtual characters (`tau3_mem_ZIrr`). -/
theorem Hypothesis.eta10_mem_ZIrr [Finite G] (hyp : Hypothesis (G := G)) :
    hyp.eta10 ∈ ZIrr G := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
  exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)

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

open scoped Classical in
/-- `F`-parameterized form of `sum_filter_erase_one_normSq_eq` (instance-free interface): any
`Finset` with the sharp-membership characterization works. -/
theorem sum_finset_sharp_normSq_eq {L : Type*} [Group L] [Finite L]
    {K : Subgroup L} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (F : Finset L) (hF : ∀ x : L, x ∈ F ↔ (x ∈ K ∧ x ≠ 1))
    (f : L → ℂ) (ψ : ClassFunction ↥K ℂ) (hagree : ∀ k : ↥K, f ↑k = ψ k)
    {n : ℕ} (hn : ClassFunction.inner ψ ψ = (n : ℂ)) :
    ∑ x ∈ F, ‖f x‖ ^ 2 = (Nat.card ↥K : ℝ) * (n : ℝ) - ‖f 1‖ ^ 2 := by
  classical
  have : Fintype L := Fintype.ofFinite L
  have hFeq : F = (Finset.univ.filter (· ∈ K)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [hFeq]
  exact sum_filter_erase_one_normSq_eq f ψ hagree hn

open scoped Classical in
/-- `F`-parameterized form of `sum_apply_erase_one_filter_subgroupOf` (instance-free
interface). -/
theorem sum_finset_sharp_transport [Finite G] {M : Type*} [AddCommMonoid M]
    {K L : Subgroup G} [Finite ↥L] (hKL : K ≤ L)
    (F : Finset ↥L) (hF : ∀ x : ↥L, x ∈ F ↔ ((x : G) ∈ K ∧ x ≠ 1))
    (f : G → M) :
    ∑ x ∈ F, f ↑x = ∑ x ∈ (Set.toFinite (sharpSubgroup K)).toFinset, f x := by
  classical
  have : Fintype ↥L := Fintype.ofFinite ↥L
  have hFeq : F = (Finset.univ.filter (· ∈ K.subgroupOf L)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter, Subgroup.mem_subgroupOf]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [hFeq]
  exact sum_apply_erase_one_filter_subgroupOf hKL f

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/HSharpChosenBase.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), a chosen `𝒮₁` base**: the distinguished reducible
`μ`-column in `CharacterDegreeCore` contains a linear irreducible character of
`H = PC` whose kernel does not contain `P`.  This base is enough for the
`η₁₀` correction; no conditional `λ` datum is needed. -/
theorem CharacterDegreeCore.exists_hSharpBase [Finite G]
    {hyp : Hypothesis (G := G)} (core : CharacterDegreeCore hyp) :
    ∃ φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥(hyp.H.subgroupOf hyp.S),
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)) := by
  have := hyp.finiteG
  obtain ⟨j, δ, θ, hj, hδ, hθirr, hθ1, hθP, hμeq, hμτ⟩ :=
    core.mu_col_tau1_eta_col_one
  exact ⟨⟨θ, hθirr⟩, hθP⟩

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10HCorrection.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.7), nonzero correction at the identity** for a chosen
`P`-nonkernel (7.6) base.  The correction is constant on `P`; evaluating at a nonidentity
element of `W₂ ≤ P` and applying the (1.10) primitive-root congruence rules out zero. -/
theorem Hypothesis.eta10_alphaCF_one_ne_zero_base_core [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ))) :
    hypothesis76AlphaCF (H_sharp_hypothesis76_base hG hyp φ₀)
        (hyp.P.subgroupOf hyp.S) hyp.eta10 1 ≠ 0 := by
  classical
  intro hzero
  obtain ⟨y', hy'⟩ : ∃ y' : ↥hyp.W2, y' ≠ 1 := by
    have : Nontrivial ↥hyp.W2 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.p_eq_card_W2]; exact hyp.p_prime.one_lt)
    exact exists_ne 1
  have hyW2 : (y' : G) ∈ hyp.W2 := y'.2
  have hy1 : (y' : G) ≠ 1 := fun h => hy' (Subtype.ext h)
  have hyP : (y' : G) ∈ hyp.P := W2_le_P hG hyp hyW2
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hyS : (y' : G) ∈ hyp.S := hPS hyP
  have hyH : (y' : G) ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.H) hyP
  have hval : hyp.eta10 ((⟨(y' : G), hyS⟩ : ↥hyp.S) : G)
      = hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) hyp.eta10 ⟨(y' : G), hyS⟩ :=
    hypothesis76_point_formula_kernel_only (H_sharp_hypothesis76_base hG hyp φ₀)
      (fun _ => rfl) (hyp.P.subgroupOf hyp.S) hyp.eta10
      (fun i _ hiP => eta10_cCoeff_base_eq_zero hG core φ₀ hφ₀P i hiP)
      ⟨(y' : G), hyS⟩
      (by rw [OddOrder.Peterfalvi.S04.mem_sharp]; exact ⟨hyH, hy1⟩)
  have hconst := hypothesis76AlphaFun_const (H_sharp_hypothesis76_base hG hyp φ₀)
    (hyp.P.subgroupOf hyp.S) hyp.eta10 ⟨(y' : G), hyS⟩
    (Subgroup.mem_subgroupOf.mpr hyP)
  have halpha0 : hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
      (hyp.P.subgroupOf hyp.S) hyp.eta10 1 = 0 := by
    simpa using hzero
  have heta0 : hyp.eta10 (y' : G) = 0 := hval.trans (hconst.trans halpha0)
  obtain ⟨z, hzint, hz⟩ := hyp.eta10_apply_sub_one_integral
    (Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne') hyW2 hy1
  rw [heta0, zero_sub] at hz
  have hdvd : (hyp.q : ℤ) ∣ (-1 : ℤ) :=
    OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd hyp.q_prime
      (Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne') hzint
      (by exact_mod_cast hz)
  have hle : (hyp.q : ℤ) ≤ 1 := Int.le_of_dvd one_pos (dvd_neg.mp hdvd)
  have hq := hyp.q_prime.one_lt
  omega

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5)/(13.7), honest Core `η₁₀` correction package on `H^#`**:
choose a `P`-nonkernel base from the Core, realize the kernel tail as a virtual character
on `H`, and assemble its integral Parseval data, inflation bound, and abelian equality case. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) :
    ∃ (α : G → ℂ) (d n s : ℕ),
      (∀ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, hyp.eta10 x = α x) ∧
      (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖α x‖ ^ 2 = (s : ℝ)) ∧
      1 ≤ n ∧ s + d ^ 2 = Nat.card ↥hyp.H * n ∧
      (hyp.p ^ hyp.q - 1) * d ^ 2 ≤ s ∧ (n = 1 → d ^ 2 = 1) := by
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨φ₀, hφ₀P⟩ := core.exists_hSharpBase
  set αS : ↥hyp.S → ℂ :=
    hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
      (hyp.P.subgroupOf hyp.S) hyp.eta10 with hαSdef
  have hHS : hyp.H ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by
        rw [hyp.S_deriv_eq_PU]
        exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    change hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]
      exact le_trans inf_le_left hUS
  refine ⟨fun g => if h : g ∈ hyp.S then αS ⟨g, h⟩ else 0, ?_⟩
  set K : Subgroup ↥hyp.S :=
    (H_sharp_hypothesis76_base hG hyp φ₀).H.subgroupOf hyp.S with hKdef
  have : Fintype ↥K := FiniteInduce.finiteSubFintype K
  set F : Finset ↥hyp.S := (Finset.univ.filter (· ∈ K)).erase 1 with hFdef
  have hFK : ∀ x : ↥hyp.S, x ∈ F ↔ (x ∈ K ∧ x ≠ 1) := fun x => by
    rw [hFdef, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h2, h1⟩,
      fun ⟨h2, h1⟩ => ⟨h1, Finset.mem_univ _, h2⟩⟩
  have hFH : ∀ x : ↥hyp.S, x ∈ F ↔ ((x : G) ∈ hyp.H ∧ x ≠ 1) := fun x => by
    rw [hFK]
    exact and_congr_left (fun _ => Subgroup.mem_subgroupOf)
  set ψ : ClassFunction ↥K ℂ :=
    ClassFunction.restrict K
      (hypothesis76AlphaCF (H_sharp_hypothesis76_base hG hyp φ₀)
        (hyp.P.subgroupOf hyp.S) hyp.eta10) with hψdef
  have hψZ : ψ ∈ ZIrr ↥K :=
    hypothesis76AlphaCF_restrict_mem_ZIrr
      (H_sharp_hypothesis76_base hG hyp φ₀) (hyp.P.subgroupOf hyp.S) hyp.eta10
      (H_sharp_hypothesis76_base_cCoeff_int hG hyp φ₀ hyp.eta10_mem_ZIrr)
  obtain ⟨n, hn⟩ := exists_nat_inner_self_of_mem_ZIrr hψZ
  obtain ⟨z, hz⟩ := OddOrder.Algebra.exists_int_apply_one_of_mem_ZIrr hψZ
  have hψ1 : ψ 1 = αS 1 := by
    rw [hψdef, ClassFunction.restrict_apply, OneMemClass.coe_one,
      hypothesis76AlphaCF_apply, hαSdef]
  have hcardK : Nat.card ↥K = Nat.card ↥hyp.H := by
    rw [hKdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show (H_sharp_hypothesis76_base hG hyp φ₀).H ≤ hyp.S from hHS)).toEquiv
  set d : ℕ := z.natAbs with hddef
  have hagree : ∀ k : ↥K, αS ↑k = ψ k := fun k => by
    rw [hψdef, ClassFunction.restrict_apply, hypothesis76AlphaCF_apply, hαSdef]
  have hbook := sum_finset_sharp_normSq_eq (K := K) F hFK αS ψ hagree hn
  have hα1 : ‖αS 1‖ ^ 2 = (d : ℝ) ^ 2 := by
    have h2 : ((d : ℕ) : ℝ) ^ 2 = ((z : ℝ)) ^ 2 := by
      rw [hddef]
      have h0 : (((z.natAbs ^ 2 : ℕ) : ℤ) : ℝ) = ((z ^ 2 : ℤ) : ℝ) := by
        exact_mod_cast Int.natAbs_sq z
      push_cast at h0
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact h0
    rw [← hψ1, hz, Complex.norm_intCast, sq_abs, ← h2]
  have hsharp_nonneg : (0 : ℝ) ≤ ∑ x ∈ F, ‖αS x‖ ^ 2 :=
    Finset.sum_nonneg (fun x _ => by positivity)
  have hd2n : d ^ 2 ≤ Nat.card ↥hyp.H * n := by
    have h0 := hsharp_nonneg
    rw [hbook] at h0
    have h1 : (d : ℝ) ^ 2 ≤ (Nat.card ↥hyp.H : ℝ) * (n : ℝ) := by
      rw [← hα1, ← hcardK]
      linarith [h0]
    exact_mod_cast h1
  set s : ℕ := Nat.card ↥hyp.H * n - d ^ 2 with hsdef
  have hsval : (s : ℝ) =
      (Nat.card ↥hyp.H : ℝ) * (n : ℝ) - (d : ℝ) ^ 2 := by
    rw [hsdef, Nat.cast_sub hd2n]
    push_cast
    ring
  have hFsum : ∑ x ∈ F, ‖αS x‖ ^ 2 = (s : ℝ) := by
    rw [hbook, hα1, hsval, hcardK]
  have hglue := sum_finset_sharp_transport (K := hyp.H) (L := hyp.S) hHS F hFH
    (fun g : G => ‖if h : g ∈ hyp.S then αS ⟨g, h⟩ else 0‖ ^ 2)
  have hGside : ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
      ‖if h : x ∈ hyp.S then αS ⟨x, h⟩ else 0‖ ^ 2 = (s : ℝ) := by
    rw [← hglue, ← hFsum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [dif_pos x.2]
  refine ⟨d, n, s, ?_, hGside, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxH, hx1⟩ := (Set.Finite.mem_toFinset _).mp hx
    have hxS : x ∈ hyp.S := hHS hxH
    change hyp.eta10 x = if h : x ∈ hyp.S then αS ⟨x, h⟩ else 0
    rw [dif_pos hxS]
    have hxsharp : ((⟨x, hxS⟩ : ↥hyp.S) : G) ∈
        OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) :=
      OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxH, hx1⟩
    have hpt := hypothesis76_point_formula_kernel_only
      (H_sharp_hypothesis76_base hG hyp φ₀) (fun _ => rfl)
      (hyp.P.subgroupOf hyp.S) hyp.eta10
      (fun i _ hiP => eta10_cCoeff_base_eq_zero hG core φ₀ hφ₀P i hiP)
      ⟨x, hxS⟩ hxsharp
    rw [hpt]
    rfl
  · by_contra hn0
    push Not at hn0
    have hn00 : n = 0 := by omega
    subst hn00
    have hzero : ∑ k : ↥K, ‖ψ k‖ ^ 2 = 0 := by
      have h := sum_normSq_eq_card_mul_inner (H := ↥K) ψ
      rw [hn] at h
      have h0 : ((∑ k : ↥K, ‖ψ k‖ ^ 2 : ℝ) : ℂ) = 0 := by
        rw [h]
        push_cast
        ring
      exact_mod_cast h0
    have hψ10 : ψ 1 = 0 := by
      have h1 : ‖ψ 1‖ ^ 2 = 0 := by
        have hle : ‖ψ 1‖ ^ 2 ≤ ∑ k : ↥K, ‖ψ k‖ ^ 2 :=
          Finset.single_le_sum (f := fun k : ↥K => ‖ψ k‖ ^ 2)
            (fun k _ => by positivity) (Finset.mem_univ 1)
        have hge : (0 : ℝ) ≤ ‖ψ 1‖ ^ 2 := by positivity
        linarith [hzero ▸ hle]
      have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      simpa using h2
    refine hyp.eta10_alphaCF_one_ne_zero_base_core hG core φ₀ hφ₀P ?_
    simpa [hψdef, ClassFunction.restrict_apply] using hψ10
  · omega
  · have hinfl := H_sharp_hypothesis76_base_alphaFun_inflation
      hG hyp φ₀ hyp.eta10
    have hHbase : (H_sharp_hypothesis76_base hG hyp φ₀).H = hyp.H := rfl
    have h1 : ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * (d : ℝ) ^ 2 ≤ (s : ℝ) := by
      rw [← hα1, ← hFsum]
      simpa [F, K, hαSdef, hHbase] using hinfl
    exact_mod_cast h1
  · intro hn1
    subst hn1
    have hn' : ClassFunction.inner ψ ψ = 1 := by
      rw [hn]
      norm_num
    obtain ⟨ε, ξ, hε, hψeq⟩ :=
      OddOrder.RepresentationTheory.exists_zsmul_irreducibleCharacter_of_inner_self_one
        hψZ hn'
    have : IsMulCommutative ↥K := by
      have hH := hyp.H_mulCommutative hG
      have e := Subgroup.subgroupOfEquivOfLe
        (show (H_sharp_hypothesis76_base hG hyp φ₀).H ≤ hyp.S from hHS)
      exact ⟨⟨fun a b => e.injective (by
        rw [map_mul, map_mul]
        exact hH.is_comm.comm (e a) (e b))⟩⟩
    have hξ1 : (ξ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        ξ.2
    have hz2 : (z : ℂ) = (ε : ℂ) := by
      rw [← hz, hψeq,
        show ((ε • (ξ : ClassFunction ↥K ℂ)) 1) =
            (ε : ℂ) * (ξ : ClassFunction ↥K ℂ) 1 from by
          rw [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.smul_apply],
        hξ1, mul_one]
    have hzε : z = ε := by exact_mod_cast hz2
    rcases hε with h | h <;>
      · rw [hddef, hzε, h]
        rfl

end

end OddOrder.Peterfalvi.S15
