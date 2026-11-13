-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.betaM_expansion
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:29:36.631247+00:00
-- url     : https://prove2.me/submissions/deeb4777-184f-4694-b955-c4574bc8fcb2

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean
--   OddOrder/Peterfalvi/S11_CaseAOddPartBound.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean
--   OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacter.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S15_SAndTGrid.lean
--   OddOrder/Peterfalvi/S15_SAndT.lean
--   OddOrder/Peterfalvi/S15_CaseBReducibleCoherence.lean
--   OddOrder/Peterfalvi/S15_CaseACoherence.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayerCore.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayer.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean
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
import Theorems.Thm_OddOrder_Peterfalvi_S11_caseA_blockScalarFacts
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_S
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_false_of_parameters_and_typeIOverNormalizerData
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_analytic_inequality_of_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_sSet_irr
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_forces_T_caseB_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseB_member
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseA
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_tauS_mu_row0_vanish_on_V
import Theorems.Thm_OddOrder_Peterfalvi_S15_typeI_caseC_dichotomy_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_dadeSupport_betaGrid_disjoint_support_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_coherent_extension_orthogonal_eta_of_mem_Sset
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseB_order_u_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S15_numeric_bounds_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S15_c_eq_one_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_numeric_parameters
import Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_mSide_dadeSupport_avoids_regular
import Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_typeIGrid_betaL_inner_eta_eq_h78_beta
import Theorems.Thm_OddOrder_Peterfalvi_S16_TypeICoherent78Data_etaGrid_projection_rigidity
import Theorems.Thm_OddOrder_Peterfalvi_S16_TypeICoherent78Data_etaGrid_projection_sub_beta_norm_one
import Theorems.Thm_OddOrder_Peterfalvi_S16_TypeICoherent78Data_etaGrid_projection_sub_beta_classification
import Theorems.Thm_OddOrder_Peterfalvi_S16_cyclotomic_ratio_gt_of_q_lt_p
import Theorems.Thm_OddOrder_Peterfalvi_S16_exists_LHypothesis
import Theorems.Thm_OddOrder_Peterfalvi_S16_main_size_bounds_structural
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_side_caseB_facts

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- The source difference `Ind 1_H - ζ` is virtual when the `Ind 1_H`
source term is virtual and the distinguished `ζ` is irreducible. -/
theorem sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L :=
  Submodule.sub_mem _ hindZ hzeta_irr.mem_ZIrr

/-- Virtuality of `Ind 1_H` and irreducibility of `ζ` supply the
virtual-character input needed by the Dade bridge for `β`. -/
theorem beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.beta ∈ ZIrr G :=
  H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr
    (H78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

/-- The Dade image defining `β` is supported on the corresponding Dade support. -/
theorem beta_support_subset_dadeSupport (H78 : Hypothesis78 G A L) :
    H78.beta.support ⊆ H78.hyp76.hyp71.hyp.dadeSupport := by
  intro g hg
  by_contra hnot
  exact hg (by
    rw [H78.beta_def]
    exact H78.hyp76.hyp71.isDadeMap.map_eq_zero_of_not_mem_dadeSupport
      H78.indMinusZetaSupp g hnot)

/-- The defining rearrangement `β = 1_G - ζ^ν + Δ`. -/
theorem beta_eq_constOne_sub_zetaImage_add_delta (H78 : Hypothesis78 G A L) :
    H78.beta =
      Hypothesis71.constOne G - H78.nu (H78.hyp76.zeta H78.zetaDistinct) +
        H78.delta := by
  rw [delta]
  abel

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- `BetaDecomp` identifies the (7.9) residual `Δ` with the weighted part plus
`Γ`. -/
theorem delta_eq_weightedNuSum_add_gamma
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    H78.delta = (hBD.a : ℂ) • H78.weightedNuSum + hBD.Gamma := by
  rw [delta, hBD.beta_eq]
  abel

/-- The residual `Δ` is orthogonal to `1_G`. -/
theorem delta_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.delta (Hypothesis71.constOne G) = 0 := by
  rw [H78.delta_eq_weightedNuSum_add_gamma hBD, ClassFunction.inner_add_left,
    ClassFunction.inner_smul_left, H78.weightedNuSum_orth_one hBD,
    hBD.Gamma_orth_one, mul_zero, add_zero]

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

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

-- ===== OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean =====
namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory OddOrder.GroupTheory OddOrder.Isaacs.Ch03

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk')

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **Peterfalvi (9.7.a): the qualitative block-scalar product embedding.**  Projection of
`caseA_blockScalarFacts`; see there for the accompanying `a`-form divisibility. -/
theorem caseA_exists_blockScalarRatioEmbedding [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    ∃ ψ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (Fin (data.q - 1) → (ZMod chief.p)ˣ),
      Function.Injective ψ :=
  (caseA_blockScalarFacts chars caseA).1

open scoped Classical in
/-- **Peterfalvi (9.7.a): imprimitive block-scalar order divisibility.**  From the case-(a) Clifford
data, the image `Ū = U/C_U(H̄)` embeds as a subgroup of `((𝔽_p)ˣ)^{q-1}`; hence its order
`u = |Ū|` divides `(p - 1)^{q-1}`.  This strengthened form retains the odd-part information used
in Peterfalvi (13.13). -/
theorem caseA_u_dvd_pred_pow [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    chars.u ∣ (chief.p - 1) ^ (data.q - 1) := by
  have : Fact chief.p.Prime := ⟨chief.p_prime⟩
  obtain ⟨ψ, hψ⟩ := caseA_exists_blockScalarRatioEmbedding chars caseA
  have hunits : Nat.card (ZMod chief.p)ˣ = chief.p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime chief.p_prime]
  have hdiv := Subgroup.card_dvd_of_injective ψ hψ
  rw [Nat.card_pi, hunits] at hdiv
  have hu : chars.u = Nat.card ↥(uActionHom data chief).range :=
    chars.u_eq_card_quotient
  rw [hu]
  simpa using hdiv

end OddOrder.Peterfalvi.S11

-- ===== OddOrder/Peterfalvi/S11_CaseAOddPartBound.lean =====
namespace OddOrder.Peterfalvi.S11

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.13), case-A odd-part divisibility.**  The imprimitive block action gives
`u ∣ (p - 1)^(q - 1)`; since `u` is odd, coprimality with `2^(q - 1)` removes that factor from
`(p - 1)^(q - 1) = 2^(q - 1) ((p - 1) / 2)^(q - 1)`. -/
theorem caseA_u_dvd_half_pred_pow [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars) :
    chars.u ∣ ((chief.p - 1) / 2) ^ (data.q - 1) := by
  have hdiv := caseA_u_dvd_pred_pow chars caseA
  have heven : 2 ∣ chief.p - 1 :=
    even_iff_two_dvd.mp (chiefFactor_p_sub_one_even (chief := chief) hG)
  have hsplit : chief.p - 1 = 2 * ((chief.p - 1) / 2) :=
    (Nat.mul_div_cancel' heven).symm
  rw [hsplit, mul_pow] at hdiv
  have hcop : Nat.Coprime chars.u (2 ^ (data.q - 1)) :=
    (Nat.coprime_two_right.mpr (u_odd hG chars)).pow_right _
  exact hcop.dvd_of_dvd_mul_left hdiv

end OddOrder.Peterfalvi.S11

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

namespace Hypothesis

/-- **Peterfalvi (13.11.b)** at the Section 15 hypothesis level: if `q ≥ 5`,
then the concrete analytic parameter satisfies `m > 7/10`. -/
theorem m_gt_seven_tenths_of_five_le_q (hyp : Hypothesis (G := G))
    (hq5 : 5 ≤ hyp.q) :
    hyp.m > (7 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_seven_tenths hq5 hyp.three_le_p

end Hypothesis

/-- **Peterfalvi (13.13)**: if case (9.7.a) holds for `S`, then
`q = 3` and `u = (p - 1)^2 / 4`.

The hypothesis is the genuine §11 `CliffordCaseAData` for the `S`-side chief factor.  Its block
decomposition supplies `u ∣ ((p - 1)/2)^(q - 1)`; (13.10), (13.11), and `c = 1` then feed the
pure elimination `caseA_numeric_parameters`. -/
theorem caseA_parameters_of_analytic_inequality [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief)) :
    hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  have hc1 := c_eq_one_of_analytic_inequality hG hyp h1310
  have hdiv := OddOrder.Peterfalvi.S11.caseA_u_dvd_half_pred_pow hG
    (hyp.mkSection11CharacterDataS hG chief) caseA
  rw [hyp.mkSection11CharacterDataS_u_eq hG chief,
    hyp.chiefFactorS_p_eq hG chief, hyp.toTypesIIIIIIVSetupS_q_eq hG] at hdiv
  have hpeven : 2 ∣ hyp.p - 1 := by
    have h := even_iff_two_dvd.mp
      (OddOrder.Peterfalvi.S11.chiefFactor_p_sub_one_even (chief := chief) hG)
    rwa [hyp.chiefFactorS_p_eq hG chief] at h
  have h1310c := h1310
  rw [hc1] at h1310c
  norm_num at h1310c
  have h1310' : (hyp.u : ℚ) >
      hyp.m * (((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ)) / (hyp.q : ℚ) := by
    have hpowcast : (((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ)) =
        (hyp.p : ℚ) ^ (hyp.q - 1) := by
      push_cast
      ring
    rw [hpowcast]
    exact h1310c
  have h13c : hyp.q = 3 →
      (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6) < (hyp.u : ℚ) := by
    intro hq3
    obtain ⟨_, _, hnum⟩ := numeric_bounds_of_analytic_inequality hyp h1310
    have h := (hnum hq3).2
    rw [hc1] at h
    simpa using h
  exact caseA_numeric_parameters hyp.three_le_p hyp.q_prime hyp.q_ne_two hpeven
    hyp.m_gt_seven_tenths_of_five_le_q h13c h1310' hdiv

/-- The `p ≡ 1 [MOD q]` divisibility part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_dvd_of_modEq_one {p q : ℕ} (hp : p.Prime)
    (hpq : p ≡ 1 [MOD q]) :
    q ∣ (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [← Nat.modEq_zero_iff_dvd]
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD q] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpq
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  exact hterms.trans (by simp [hsum_one])

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

-- ===== OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Prime-`TI` row-`0` cross-column distinctness** (issue 9076 piece 4c-4): distinct columns of
row `0` carry distinct `μ`-entries, `μ_{0j} ≠ μ_{0,#1}` for `j ≠ #1`.  This is the cross-column
injectivity of the prime-`TI` residue grid: the `μ_{ij}` are pairwise-distinct irreducibles across
the *whole* grid (Coq: the residues `prTIres i j` are distinct for distinct `(i, j)`).  The
`Hypothesis` structure records only the *within-column* distinctness `mu_col_injective`; this
row-direction distinctness is the missing prime-`TI` fact.  Prime-`TI` theory, cf. issue 9014. -/
theorem Hypothesis.mu_row0_ne [Finite G] (hyp : Hypothesis (G := G)) {j : Fin hyp.p}
    (hj : j ≠ ⟨1, by have := hyp.three_le_p; omega⟩) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j
      ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
  classical
  intro heq
  -- The diagonal value `⟨μ_{0,#1}, μ_{0,#1}⟩ = 1` (irreducibility, `mu_irreducible`).
  have hdiag : OddOrder.RepresentationTheory.ClassFunction.inner
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 1 :=
    (hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩
      ⟨1, by have := hyp.three_le_p; omega⟩).inner_self_eq_one
  -- The off-diagonal (row-`0` cross-column) value `⟨μ_{0j}, μ_{0,#1}⟩ = 0` (`j ≠ #1`) is the
  -- prime-`TI` grounding: the full-grid orthonormality field `mu_orthonormal` (b-side, issues
  -- 9076/3002/9014), discharged in the spine by `Section16CharacterData.muS_orthonormal`
  -- (`muS = columnFamily.mu = residueS.mu2`, cf. `S13_PrimeTIResidueBridge`).
  have hoff : OddOrder.RepresentationTheory.ClassFunction.inner (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 := by
    rw [hyp.mu_orthonormal]
    exact if_neg (fun hc => hj hc.2)
  rw [heq, hdiag] at hoff
  exact one_ne_zero hoff

/-- **Prime-`TI` support pin, proven** (Coq `prDade_sub_TIirr_on`, `PFsection4.v`): the `μ`-column
difference `μ_{0j} − μ_{0,#1}` is supported inside `A₀(S) = A(S) ∪ V^S` — its support meets `S`
only in `P^# ∪ V_S`, because the two prime-`TI` residues share the same `1_S`-part off `A₀(S)` and
it cancels in the difference.  This is the `S`-side instance of Coq `prDade_sub_TIirr_on`
(`μ2_{ij} − μ2_{ik} ∈ 'CF(S, 'A0)`).

**Honest signature (issue 9076, 2026-07-11)**: carries `(hj0 : (j:ℕ) ≠ 0)` — the unrestricted
`∀ j` form is *false* at the trivial column `j = 0` (`μ_{00}(1) = 1 ≠ μ_{0,#1}(1)`, and `1 ∉ A₀`).
The sole consumer `tauS_mu_row0_cross` (S15_SAndT) passes its `_hj`.

**Fully discharged (2026-07-11)**: the support claim is the `(13.18)` grounding field
`mu_diff_support` (issue 9081: producer-supplied by the proven
`Section16CharacterData.muS_diff_support`, Dade-free via `hyp46SmpCore`), and the degree
hypothesis is the proven per-entry degree `mu_apply_one_eq_u` (Pf (13.3)(a): `μ_{ij}(1) = u` for
`j ≠ 0`, via `mu_j_isIndPC` + `H_index_eq_uq`) — the same two steps Coq's `defGamma` uses
(`prDade_sub_TIirr` + the `FTprTIred1` `mulfI`-cancellation, `PFsection13.v:1909`). -/
theorem Hypothesis.tauS_mu_row0_diff_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj0 : (j : ℕ) ≠ 0) :
    (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
  hyp.mu_diff_support ⟨0, hyp.q_prime.pos⟩
    (fun h => hj0 (congrArg Fin.val h))
    (fun h => one_ne_zero (congrArg Fin.val h))
    ((hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j
        (fun h => hj0 (congrArg Fin.val h))).trans
      (hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩
        ⟨1, by have := hyp.three_le_p; omega⟩
        (fun h => one_ne_zero (congrArg Fin.val h))).symm)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacter.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.8)/(5.3) prime-`TI` Dade cross-relation, `S`-side row-`0` form**:
`τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` for `j ≠ 0`.

This is Coq `prDade_sub_TIirr` (`PFsection4.v:870`) `τ(μ2_{ij} − μ2_{ik}) = δ_j·(η_{ij} − η_{ik})`
specialized to row `i = 0`, columns `j` and `#1`, with the `FT`-context sign `δ_j = 1`.  It is the
single deep input behind (13.18.c)'s `j`-independence `gammaGrid_defGamma`.

✅ **Now on the correct Dade map** (issue 9076, 2026-07-08): `τ_S` is `dadeIntegralCharacterMap`
of the honest **`'A0(S)`-Dade** `dadeHypS0` (support `A₀(S) = A(S) ∪ V^S`), **not** the smaller
`'A(S)`-Dade `dadeHypS`.  The `μ`-column difference `μ_{0j} − μ_{01}` is supported on `P^# ∪ V_S`
(Coq `prDade_sub_TIirr_on`), and `V_S ⊄ S' ⊇ A(S)`, so with the old `dadeHypS` map the `V_S`-part
fell in the arbitrary linear-extension region and the statement was **unprovable as stated**; the
`'A0`-Dade correction fixes that (`dadeHypS0` inherits one deep FT-support pin,
`S10.not_isConj_typePACore_typePV`).

The route: `X := τ_S(μ-diff)` has `‖X‖² = 2` (Dade isometry) and `X ∈ ZIrr`; it agrees with
`η_{0j} − η_{01}` on the regular set via `τ_S = Ind_S^G` on `A₀`-supported (`normedTI 'A0`,
`H = ⊥`) + the prime-`TI` `μ`-value `μ_{0j}|_V = ω`-value (Coq `prTIirr_id`, prime-`TI` theory,
cf. 9014); then `X = η_{0j} − η_{01}` by `S16.eta_diff_rigidity` (Peterfalvi (3.8), issue 9076
piece 4b). -/
theorem tauS_mu_row0_cross [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ j
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
  classical
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData) with hD
  by_cases hj1 : j = ⟨1, by have := hyp.three_le_p; omega⟩
  · -- Trivial column `j = #1`: both `μ`- and `η`-differences vanish, and `τ_S 0 = 0`.
    simp only [hj1, sub_self, map_zero]
  · -- `j ≠ #1`: `X := τ_S(μ_{0j} − μ_{0,#1})` is a norm-`2` `ZIrr` character agreeing with
    -- `η_{0j} − η_{0,#1}` on the regular set `V`, so `S16.eta_diff_rigidity` (3.8) pins it.
    have hμaIrr : IsIrreducibleCharacter (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) :=
      hyp.mu_irreducible _ _
    have hμbIrr : IsIrreducibleCharacter
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) :=
      hyp.mu_irreducible _ _
    have hμne : hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ :=
      hyp.mu_row0_ne hj1
    have hsupp := hyp.tauS_mu_row0_diff_support hG j _hj
    have hZIrrS : (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        ∈ ZIrr (↥hyp.S) :=
      (ZIrr (↥hyp.S)).sub_mem hμaIrr.mem_ZIrr hμbIrr.mem_ZIrr
    -- (a) `X ∈ ZIrr G` (Dade sends supported virtual characters to virtual characters, `(2.6.b)`).
    have hXZ : D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) ∈ ZIrr G :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypS0 hG) hsupp hZIrrS
    -- (b) `‖μ_{0j} − μ_{0,#1}‖² = 2` (two distinct irreducibles).
    have hinner : ∀ φ ψ : ClassFunction ↥hyp.S ℂ, IsIrreducibleCharacter φ →
        IsIrreducibleCharacter ψ → ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥hyp.S)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥hyp.S)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have h_ab : ClassFunction.inner (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 := by
      rw [hinner _ _ hμaIrr hμbIrr, if_neg hμne]
    have h_ba : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [hinner _ _ hμbIrr hμaIrr, if_neg (Ne.symm hμne)]
    have hnorm2 : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 2 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h_ab, h_ba,
        hμaIrr.inner_self_eq_one, hμbIrr.inner_self_eq_one]
      ring
    have hX2 : ClassFunction.inner
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩))
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) = 2 := by
      rw [hD, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS0 hG) hsupp hsupp]
      exact hnorm2
    -- (c) `X − (η_{0j} − η_{0,#1})` vanishes on the regular set `V` (prime-`TI` `V`-value pin).
    have hvanish : ∀ x ∈ conjClassSet
          ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
              - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
          - ((1 : ℤ) : ℂ) • (hyp.eta ⟨0, hyp.q_prime.pos⟩ j
              - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) x = 0 := by
      intro x hx
      have hv := hyp.tauS_mu_row0_vanish_on_V hG hnoV j _hj x hx
      simpa [hD] using hv
    -- (3.8) rigidity: a norm-`2` `ZIrr` character agreeing with `η_{0j} − η_{0,#1}` on `V` is it.
    have hrig := OddOrder.Peterfalvi.S16.eta_diff_rigidity hyp hXZ hX2
      ⟨0, hyp.q_prime.pos⟩ hj1 (s := (1 : ℤ)) (Or.inl rfl) hvanish
    rw [Int.cast_one, one_smul] at hrig
    exact hrig

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c), `j`-independence** (`defGamma`): for every column `j ≠ 0`, the bridge residual
`τ_S(β_j) − 1_G + η_{0j}` equals the fixed gap `Γ = GammaGrid` (defined at column `#1`).

This is exactly Peterfalvi (13.18.c)'s "`Γ` is independent of `j`" (Coq `defGamma`,
`PFsection13.v:1905`), **NOT** grid-orthogonality: the previous scaffold field
`Gamma_independent : ⟨Γ, η_{ik}⟩ = 0` was an **overstatement** (issue 3003), refuted by the genuine
(13.18.d) `X + Y` decomposition where `Γ`'s grid-component `X` is nonzero.

Proof (sorry-free glue, one isolated obligation): `τ_S(β_j) − τ_S(β_{#1}) = τ_S(β_j − β_{#1})` by
`ℤ`-linearity of the Dade map (`map_sub`), and `β_j − β_{#1} = μ_{01} − μ_{0j} = −(μ_{0j} − μ_{01})`
(both share the `Ind_{PW₁}^S 1` positive part), so `τ_S(β_j − β_{#1}) = −(η_{0j} − η_{01}) =
η_{01} −
η_{0j}` by the (4.8)/(5.3) cross-relation `tauS_mu_row0_cross`.  Cancelling the `−1_G`'s and
`abel` closes the goal. -/
theorem gammaGrid_defGamma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) (betaGrid hyp j)
        - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + hyp.eta ⟨0, hyp.q_prime.pos⟩ j
      = GammaGrid hG hyp := by
  have hcross := tauS_mu_row0_cross hG hnoV hyp j hj
  have hbeta : betaGrid hyp j - betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩
      = -(hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) := by
    simp only [betaGrid]; abel
  have key : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) (betaGrid hyp j)
      - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
        - hyp.eta ⟨0, hyp.q_prime.pos⟩ j := by
    rw [← map_sub, hbeta, map_neg, hcross]; abel
  simp only [GammaGrid, tauSbetaGrid]
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData) with hD
  rw [← sub_eq_zero, show
      (D (betaGrid hyp j) - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        - (D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
          - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = (D (betaGrid hyp j) - D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩))
        - (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) by abel, key, sub_self]

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_PairingCoherence.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- The zeta family of `h78` is the placed induced family (definitional). -/
theorem h78_zeta_eq (i : Fin (data.n + 1)) :
    (data.h78 hG).hyp76.zeta i = data.zeta i := rfl

/-- The distinguished index of `h78` is `0` (definitional). -/
theorem h78_zetaDistinct_eq : (data.h78 hG).zetaDistinct = 0 := rfl

/-- The principal index of `h78` is `ind1H` (definitional). -/
theorem h78_ind1H_eq : (data.h78 hG).ind1H = data.ind1H := rfl

/-- The coherent extension of `h78` is the bundle's coherence extension
(definitional). -/
theorem h78_nu_eq : (data.h78 hG).nu = data.coh.extension := rfl

/-- The kernel of `h78`'s (7.6) layer is the Fitting kernel (definitional). -/
theorem h78_H_eq : (data.h78 hG).hyp76.H = data.kernel := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is irreducible** (Frobenius kernel induction,
[Is] Thm 6.34). -/
theorem h78_zeta_irreducible :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) := by
  have := data.kernelIn_normal
  rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

/-- **The induced principal `ζ_{ind1H} = Ind 1_H` is a virtual character.** -/
theorem h78_ind_mem_ZIrr :
    (data.h78 hG).hyp76.zeta (data.h78 hG).ind1H ∈ ZIrr ↥L := by
  have := data.kernelIn_normal
  rw [data.h78_ind1H_eq, data.h78_zeta_eq]
  exact ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr

set_option backward.isDefEq.respectTransparency false in
/-- **The conjugate `ζ̄_0` is a family member**: there is `j₁ ≠ ind1H` with
`ζ_{j₁} = ζ̄_0` (`conjPerm` of the distinguished source is covered). -/
theorem exists_conjIndex :
    ∃ j₁, j₁ ≠ (data.h78 hG).ind1H ∧
      (data.h78 hG).hyp76.zeta j₁
        = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  have := data.kernelIn_normal
  have hconj_eq : ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj
      = ClassFunction.induce data.kernelIn
          ((IrreducibleCharacter.conjPerm _ (data.θ 0)) : ClassFunction _ ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (data.θ 0)).symm
  obtain ⟨j₁, hj₁_range⟩ := data.cover (IrreducibleCharacter.conjPerm _ (data.θ 0))
  have hj₁_conj : (data.h78 hG).hyp76.zeta j₁
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [data.h78_zeta_eq, hconj_eq]; exact hj₁_range
  refine ⟨j₁, ?_, hj₁_conj⟩
  intro hj1
  apply data.ind1H_ne_zero
  have hzeta_inj : Function.Injective (data.h78 hG).hyp76.zeta := data.inj
  refine (hzeta_inj ?_).symm
  -- `ζ_{ind1H}` is real (`Ind 1_H`), and `ζ_{ind1H} = ζ_{j₁} = ζ̄_0`.
  have e1 : (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [← show j₁ = (data.h78 hG).ind1H from hj1]; exact hj₁_conj
  have e2 : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  calc (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
      = ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj := by
        rw [e1, ClassFunction.conj_conj]
    _ = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := e2

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is not real** (odd order): it is a nontrivial irreducible
(degree `[L:H] > 1`) of the odd-order group `L`. -/
theorem h78_zeta_ne_conj (hodd : Odd (Nat.card G)) :
    (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ≠ ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  have := data.kernelIn_normal
  have hirr := data.h78_zeta_irreducible hG
  have hodd_L : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  -- The kernel is proper (complement nontrivial), so `[L:H] > 1`.
  have hK_ne_top : data.kernelIn ≠ ⊤ := by
    intro hKtop
    refine data.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := data.hFrob.isComplement.disjoint
    rw [show (data.typeIHyp.typeI.typeF.H).subgroupOf L = data.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (data.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  have hdeg : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct) (1 : ↥L)
      = ((data.kernelIn).index : ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
    exact data.deg0
  have hne_triv : (⟨(data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct), hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
        = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : (((data.kernelIn).index : ℂ)) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    exact absurd (by exact_mod_cast hone : (data.kernelIn).index = 1) (by omega)
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

/-- **Members of `ℤ[S]` vanishing at `1` are `A(L)`-supported** (the `hspan` input of
`extension_mapRingEquiv_comm`): each `Ind θ ∈ S` vanishes off the normal kernel
(`Sset_vanishes_off_H`), so `ℤ[S] ⊆ {ψ | supp ψ ⊆ H}` by span induction; vanishing at `1`
then lands the support in `H^# = A(L)`. -/
theorem zSpan_Sset_support_subset (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan data.typeIHyp.Sset) (h1 : φ 1 = 0) :
    φ.support ⊆ data.typeIHyp.A := by
  have := data.kernelIn_normal
  -- `ℤ[S] ⊆ {ψ | ψ.support ⊆ kernelIn}` by span induction.
  have hsuppH : ∀ ψ ∈ OddOrder.Peterfalvi.S07.zSpan data.typeIHyp.Sset,
      ψ.support ⊆ (data.kernelIn : Set ↥L) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        intro g hg
        rw [ClassFunction.mem_support] at hg
        by_contra hgK
        exact hg (OddOrder.Peterfalvi.S14.Sset_vanishes_off_H data.typeIHyp hx
          (fun hmem => hgK (Subgroup.mem_subgroupOf.mpr hmem)))
    | zero => intro g hg; rw [ClassFunction.mem_support] at hg; exact absurd rfl hg
    | add x y _ _ hx hy =>
        intro g hg
        rcases ClassFunction.support_add_subset x y hg with h | h
        · exact hx h
        · exact hy h
    | smul c x _ hx =>
        intro g hg
        refine hx ?_
        rw [ClassFunction.mem_support] at hg ⊢
        intro hxg
        apply hg
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hxg, mul_zero]
  intro g hg
  have hgH : g ∈ data.kernelIn := hsuppH φ hφ hg
  have hg1 : g ≠ 1 := by
    rintro rfl; exact (ClassFunction.mem_support.mp hg) h1
  change g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) g).mpr ⟨hgH, hg1⟩

/-- **The family `S` consists of irreducibles** (Frobenius kernel induction). -/
theorem Sset_subset_irreducible :
    data.typeIHyp.Sset ⊆ irreducibleCharacters ↥L := by
  have := data.kernelIn_normal
  rintro φ ⟨θ', hθ'_ne, rfl⟩
  exact mem_irreducibleCharacters.mpr
    (isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob θ' hθ'_ne)

/-- **The family `S` is closed under complex conjugation** (`Ind θ̄ = (Ind θ)‾`, and
`θ̄ ≠ 1` for `θ ≠ 1`). -/
theorem Sset_closedUnderConjugate {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ data.typeIHyp.Sset) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ ∈ data.typeIHyp.Sset := by
  have := data.kernelIn_normal
  obtain ⟨θ', hθ'_ne, rfl⟩ := hφ
  have hbridge : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ))
      = (ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ)).conj := by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  rw [hbridge, conj_induce]
  refine ⟨IrreducibleCharacter.conjPerm _ θ', ?_, ?_⟩
  · -- `θ̄' ≠ 1`: conjugating `θ̄' = 1` gives `θ' = 1̄ = 1`.
    intro hconj_triv
    refine hθ'_ne (IrreducibleCharacter.ext ?_)
    have hcoe := congrArg IrreducibleCharacter.toClassFunction hconj_triv
    rw [show (IrreducibleCharacter.conjPerm _ θ').toClassFunction
        = (θ' : ClassFunction ↥data.kernelIn ℂ).conj
      from IrreducibleCharacter.conjPerm_apply_coe θ'] at hcoe
    calc (θ' : ClassFunction ↥data.kernelIn ℂ)
        = ((θ' : ClassFunction ↥data.kernelIn ℂ).conj).conj := (ClassFunction.conj_conj _).symm
      _ = ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
            ClassFunction _ ℂ).conj := by rw [hcoe]
      _ = ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
            ClassFunction _ ℂ) := trivialClassFunction_isReal
  · exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe θ').symm

/-- **The coherent extension commutes with complex conjugation on `S`**
(Peterfalvi (5.9)(a) via `extension_mapRingEquiv_comm`). -/
theorem coherence_extension_conj (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ data.typeIHyp.Sset)
    (h2 : ∃ ψ ∈ data.typeIHyp.Sset, ψ ≠ χ) :
    (data.coh.extension χ).conj = data.coh.extension χ.conj := by
  have hbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hbridgeL : ∀ X : ClassFunction ↥L ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  rw [hbridgeG (data.coh.extension χ), hbridgeL χ]
  exact data.coh.extension_mapRingEquiv_comm subset_rfl data.Sset_subset_irreducible
    (fun φ hφ h1 => data.zSpan_Sset_support_subset hG hφ h1)
    Complex.conjAe.toRingEquiv (fun φ hφ => data.Sset_closedUnderConjugate hφ)
    (fun φ hφ => data.coh.extension_mem_ZIrr φ (Submodule.subset_span hφ)) hχS h2

/-- **The conjugate of any nontrivial family member is a family member**:
for `i ≠ ind1H` there is `i' ≠ ind1H` with `ζ_{i'} = ζ̄_i`. -/
theorem exists_conjIndex_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    ∃ i', i' ≠ (data.h78 hG).ind1H ∧
      (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj := by
  have := data.kernelIn_normal
  have hconj_eq : ((data.h78 hG).hyp76.zeta i).conj
      = ClassFunction.induce data.kernelIn
          ((IrreducibleCharacter.conjPerm _ (data.θ i)) : ClassFunction _ ℂ) := by
    rw [data.h78_zeta_eq, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (data.θ i)).symm
  obtain ⟨i', hi'_range⟩ := data.cover (IrreducibleCharacter.conjPerm _ (data.θ i))
  have hi'_conj : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj := by
    rw [data.h78_zeta_eq, hconj_eq]; exact hi'_range
  refine ⟨i', ?_, hi'_conj⟩
  intro hi'1
  -- else `ζ̄_i = ζ_{ind1H} = Ind 1_H` is real, so `ζ_i = Ind 1_H`, contra `i ≠ ind1H`.
  have hind_real : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  refine hi (data.inj ?_)
  have h1 : ((data.h78 hG).hyp76.zeta i).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    rw [← hi'_conj, hi'1]
  calc (data.h78 hG).hyp76.zeta i
      = (((data.h78 hG).hyp76.zeta i).conj).conj := (ClassFunction.conj_conj _).symm
    _ = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by rw [h1, hind_real]

/-- **No nontrivial family member is real** (odd order): `ζ_i ≠ ζ̄_i` for `i ≠ ind1H`. -/
theorem zeta_ne_conj_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hodd : Odd (Nat.card G)) :
    (data.h78 hG).hyp76.zeta i ≠ ((data.h78 hG).hyp76.zeta i).conj := by
  have := data.kernelIn_normal
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial hi)
  have hodd_L : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hK_ne_top : data.kernelIn ≠ ⊤ := by
    intro hKtop
    refine data.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := data.hFrob.isComplement.disjoint
    rw [show (data.typeIHyp.typeI.typeF.H).subgroupOf L = data.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (data.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  -- `ζ_i(1) = [L:H]·θ_i(1) ≥ [L:H] > 1`, so `ζ_i` is nontrivial.
  obtain ⟨di, hdi_pos, hdi⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  have hdeg : (data.h78 hG).hyp76.zeta i (1 : ↥L)
      = ((data.kernelIn).index : ℂ) * (di : ℂ) := by
    rw [data.h78_zeta_eq]
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) = _
    rw [ClassFunction.induce_apply_one, hdi]
  have hne_triv : (⟨(data.h78 hG).hyp76.zeta i, hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (data.h78 hG).hyp76.zeta i = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : ((data.kernelIn).index : ℂ) * (di : ℂ) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    have : (data.kernelIn).index * di = 1 := by exact_mod_cast hone
    have h1 : (data.kernelIn).index = 1 := by
      rcases Nat.eq_one_of_mul_eq_one_right this with h; omega
    omega
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

set_option backward.isDefEq.respectTransparency false in
/-- **`ζ_i − ζ̄_i` is supported on `A(L)`** for any `i ≠ ind1H`. -/
theorem zeta_sub_conj_support_at (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {i i' : Fin (data.n + 1)}
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ((data.h78 hG).hyp76.zeta i - (data.h78 hG).hyp76.zeta i').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
  have := data.kernelIn_normal
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hi', ClassFunction.conj_apply] at hx
  refine (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) x).mpr ⟨?_, ?_⟩
  · by_contra hxH
    apply hx
    rw [(data.h78 hG).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH, star_zero, sub_zero]
  · intro hx1
    apply hx
    rw [hx1]
    -- `ζ_i(1)` is real (`induce_apply_one_star`).
    have hreal : star ((data.h78 hG).hyp76.zeta i (1 : ↥L))
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) := by
      rw [data.h78_zeta_eq]
      exact induce_apply_one_star data.kernelIn (data.θ i)
    rw [hreal, sub_self]

/-- **`ζ_i^ν − ζ̄_i^ν` is supported in the Dade support** for any `i ≠ ind1H`. -/
theorem nu_zeta_sub_conj_support_at (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
        - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')).support
      ⊆ (data.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  have := data.kernelIn_normal
  have hzi_mem : (data.h78 hG).hyp76.zeta i ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]; exact data.zeta_mem_Sset hi
  have hi'_mem : (data.h78 hG).hyp76.zeta i' ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]
    exact data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hsupp' : ((data.h78 hG).hyp76.zeta i
        - (1 : ℂ) • (data.h78 hG).hyp76.zeta i').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
    rw [one_smul]; exact data.zeta_sub_conj_support_at hG hi'
  have hagree := coherence_hagree_dadeMap data.typeIHyp.dadeData.dade
    data.coh hzi_mem hi'_mem (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  have heq : (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
      - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')
      = (data.typeIHyp.dadeData.dade.fullDadeIsometryData).toDadeMap
          ⟨_, (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [data.h78_nu_eq,
      ← one_smul ℂ (data.coh.extension ((data.h78 hG).hyp76.zeta i'))]
    exact hagree.symm
  rw [heq]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  have hdade := (data.typeIHyp.dadeData.dade.fullDadeIsometryData
).toDadeIsometryData.isDadeMap
  exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)

/-- **Each `ζ_i^ν` (`i ≠ ind1H`) is a unit-norm virtual character.** -/
theorem nu_zeta_norm_one {i : Fin (data.n + 1)} (hi : i ≠ (data.h78 hG).ind1H) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)) = 1 := by
  have := data.kernelIn_normal
  rw [(data.h78 hG).nu_isometry i i hi hi]
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial (by rw [← data.h78_ind1H_eq hG]; exact hi))
  exact IsIrreducibleCharacter.inner_self_eq_one hirr

/-- **Each nontrivial family member induces irreducibly** (general-index form of
`h78_zeta_irreducible`). -/
theorem zeta_irreducible_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
  have := data.kernelIn_normal
  rw [data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
    (data.theta_ne_trivial hi)

/-- **`⟨ζ_i^ν, ζ̄_i^ν⟩ = 0`**: the conjugate pair is orthonormal (`ν`-isometry +
distinct irreducibles). -/
theorem nu_zeta_inner_nu_conj_eq_zero (hodd : Odd (Nat.card G))
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')) = 0 := by
  rw [(data.h78 hG).nu_isometry i i' hi hi'_ne]
  have hirr_i := data.zeta_irreducible_at hG hi
  have hirr_i' : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i') :=
    data.zeta_irreducible_at hG (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hne : (data.h78 hG).hyp76.zeta i ≠ (data.h78 hG).hyp76.zeta i' := by
    rw [hi']
    exact data.zeta_ne_conj_at hG hi hodd
  have h := irreducibleCharacter_inner_eq_ite
    (⟨_, hirr_i⟩ : IrreducibleCharacter ↥L) ⟨_, hirr_i'⟩
  rwa [if_neg (fun heq => hne (congrArg Subtype.val heq))] at h

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S15_SAndTGrid.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19), `φ` existence**: the family `𝓛 = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1}` has a member of
degree `e = [L : H]` ("the existence of `φ` is clear"): the nontrivial solvable kernel `H` has a
nontrivial degree-one character `θ`
(`exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`); `Ind_H^L θ` lies in
`𝓛` by definition, with degree `(Ind_H^L θ)(1) = [L:H]·θ(1) = e` (`induce_apply_one`).  (The
membership already witnesses irreducibility demands downstream via the Frobenius inertia
argument packaged in `𝓛 ⊆ Irr L`.) -/
theorem exists_Sset_apply_one_eq_index [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    ∃ φ : ClassFunction ↥L ℂ, φ ∈ typeISetup.Sset ∧
      φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
  classical
  obtain ⟨frob₀, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV typeISetup.maximal
    ⟨typeISetup.typeI⟩
  -- both Frobenius kernels are `L_F`
  have hHeq : frob₀.typeI.typeF.H = typeISetup.typeI.typeF.H :=
    frob₀.typeI.typeF.H_eq.trans typeISetup.typeI.typeF.H_eq.symm
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((typeISetup.typeI.typeF.H).subgroupOf L) frob₀.complement := by
    have h := frob₀.frobenius
    rwa [hHeq] at h
  -- the kernel is a nontrivial solvable group, so it has a nontrivial linear character
  have : Group.IsSolvable ↥L := hG.isSolvable_of_lt_top L
    (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp typeISetup.maximal).1)
  have : Nontrivial ↥((typeISetup.typeI.typeF.H).subgroupOf L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hfrob.ne_bot_kernel
  have hcomm : commutator ↥((typeISetup.typeI.typeF.H).subgroupOf L) ≠ ⊤ :=
    ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial
      (G := ↥((typeISetup.typeI.typeF.H).subgroupOf L)))
  obtain ⟨θ, hθ_ne, hθ1⟩ :=
      OddOrder.Peterfalvi.S08.exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top
    hcomm
  refine ⟨ClassFunction.induce ((typeISetup.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction _ ℂ), ⟨θ, hθ_ne, rfl⟩, ?_⟩
  rw [ClassFunction.induce_apply_one, hθ1, mul_one, typeISetup.typeI.typeF.H_eq]

/-- `typeIBetaL` is literally `τ₁(Ind_H^L 1_H − φ)` under **any** ambient instances — the
`FiniteInduce`-scoped instances used in the definition agree with the caller's by
`Subsingleton`.  Bridges the `GridData.betaL_eq` field. -/
theorem typeIBetaL_eq_tau_induce_sub [Finite G] {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) (φ : ClassFunction ↥L ℂ) :
    ∀ [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
      [Invertible (Nat.card ↥((typeISetup.H).subgroupOf L) : ℂ)],
      typeIBetaL typeISetup φ = typeISetup.tau
        (ClassFunction.induce ((typeISetup.H).subgroupOf L)
          (trivialClassFunction ↥((typeISetup.H).subgroupOf L)) - φ) := by
  intro _ _ _
  unfold typeIBetaL
  repeat' first
    | rfl
    | exact Subsingleton.elim _ _
    | congr 1

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`β_L^τ` is supported in `Ã(A(L))`**: the input `Ind_H^L 1 − φ` is `A(L)`-supported — at
`1` the value is `e − e = 0` (`induce_apply_one` + the degree hypothesis), and off `1` its
support lies in nontrivial kernel-conjugates (`support`s of both `Ind` terms), which land in
`A(L)` by `H^# ⊆ A(L)` (`sharpSubgroup_H_subset_typeIA`) and the `L`-conjugation invariance of
`A(L)` (`L_normalizes_A`).  Hence the Dade lift agrees with the (2.5) Dade map there
(`dadeIntegralCharacterMap_apply_of_support`), which vanishes off `Ã(A(L)) = dadeSupport`
(`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`). -/
theorem typeIBetaL_support_subset_dadeSupport [Finite G] {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) (φ : ClassFunction ↥L ℂ)
    (hφ : φ ∈ typeISetup.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (typeIBetaL typeISetup φ).support ⊆ typeISetup.dadeData.dade.dadeSupport := by
  classical
  set H' : Subgroup ↥L := (typeISetup.H).subgroupOf L with hH'def
  set ι : ClassFunction ↥L ℂ :=
    ClassFunction.induce H' (trivialClassFunction ↥H') with hιdef
  have hsupp : (ι - φ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typeIA L typeISetup.typeI) L := by
    intro z hz
    have hzne : (ι - φ) z ≠ 0 := hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      apply hzne
      rw [ClassFunction.sub_apply, hιdef, ClassFunction.induce_apply_one,
        trivialClassFunction_apply, mul_one, hdeg]
      have hHeq : H' = (maxNilpotentNormalHall L).subgroupOf L := by
        rw [hH'def]
        change (typeISetup.typeI.typeF.H).subgroupOf L = _
        rw [typeISetup.typeI.typeF.H_eq]
      rw [hHeq, sub_self]
    have hzc : z ∈ OddOrder.RepresentationTheory.ClassFunction.conjugatesInto H' := by
      by_contra hnotc
      apply hzne
      rw [ClassFunction.sub_apply]
      obtain ⟨θ, -, hφeq⟩ := hφ
      have hφz : ClassFunction.induce ((typeISetup.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((typeISetup.typeI.typeF.H).subgroupOf L) ℂ) z = 0 :=
        ClassFunction.induce_eq_zero_of_not_conjugatesInto _ hnotc
      rw [hιdef, ClassFunction.induce_eq_zero_of_not_conjugatesInto _ hnotc, hφeq, hφz,
        sub_zero]
    obtain ⟨c, hc⟩ := hzc
    have hcne : c⁻¹ * z * c ≠ 1 := by
      intro h1
      apply hz1
      have h2 := congrArg (fun w => c * w * c⁻¹) h1
      simpa [mul_assoc] using h2
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    have hmem : ((c⁻¹ * z * c : ↥L) : G) ∈ sharpSubgroup typeISetup.typeI.typeF.H :=
      ⟨Subgroup.mem_subgroupOf.mp hc, fun h1 => hcne (Subtype.ext h1)⟩
    have hA := sharpSubgroup_H_subset_typeIA typeISetup.typeI hmem
    have hconjA := typeISetup.dadeData.dade.L_normalizes_A c hA
    simpa [mul_assoc] using hconjA
  intro x hx
  by_contra hnot
  apply hx
  change typeIBetaL typeISetup φ x = 0
  rw [typeIBetaL,
    show typeISetup.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        typeISetup.dadeData.dade
        (typeISetup.dadeData.dade.fullDadeIsometryData) from rfl,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support _ _ hsupp]
  exact (typeISetup.dadeData.dade.isDadeMap_dadeMap).map_eq_zero_of_not_mem_dadeSupport _ _ hnot

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a), `β_L^τ`-column instance**: the (13.19.a) support disjointness for the specific
`Ã(L)`-supported `β_L^τ = typeIBetaL φ` (`typeIBetaL_support_subset_dadeSupport`), a thin instance
of the general `dadeSupport_betaGrid_disjoint_support`. -/
theorem typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ))
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    Disjoint (typeIBetaL typeISetup φ).support
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
        ((hyp.dadeHypS0 _hG).fullDadeIsometryData)
        (betaGrid hyp j)).support :=
  dadeSupport_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1 typeISetup
    (typeIBetaL typeISetup φ)
    (typeIBetaL_support_subset_dadeSupport typeISetup φ _hφ _hdeg) j hj

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a) support disjointness**: `Ã(L) ∩ (P^G ∪ W^G) = ∅` — the order of an `Ã(L)`-element
is divisible by a prime divisor of `|H|`, and `|H|` is coprime to `p q` ((8.17.a)); `β_L^τ` is
supported in `Ã(L)`-classes while `β_S^τ` is supported in `P^# ∪ (W∖(W₁∪W₂))^G` ((13.18.a)).
The column-`#1` instance of `typeIBetaL_dadeS_betaGrid_disjoint_support`. -/
theorem typeIBetaL_betaS_disjoint_support_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    Disjoint (typeIBetaL typeISetup φ).support (tauSbetaGrid _hG hyp).support := by
  rw [tauSbetaGrid]
  exact typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1
    typeISetup φ _hφ _hdeg ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c), first clause (row form), difference core** (Coq `betaLeta`):
`(β_L^τ, η_{0j} − η_{0j'}) = 0` for `j, j' ≠ 0`.  By (13.18.c) `j`-independence
(`gammaGrid_defGamma` at `j` and `j'`), `η_{0j} − η_{0j'} = τ_S(β_{j'}) − τ_S(β_j)`; each
`(β_L^τ, τ_S(β_j))` vanishes by the (13.19.a) support disjointness
(`typeIBetaL_dadeS_betaGrid_disjoint_support`). -/
theorem typeIBetaL_inner_eta_row_sub_eq_zero_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ))
    (j j' : Fin hyp.p) (hj : (j : ℕ) ≠ 0) (hj' : (j' : ℕ) ≠ 0) :
    ClassFunction.inner (typeIBetaL typeISetup φ)
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j - hyp.eta ⟨0, hyp.q_prime.pos⟩ j') = 0 := by
  classical
  have h1 := gammaGrid_defGamma _hG hnoV hyp j hj
  have h2 := gammaGrid_defGamma _hG hnoV hyp j' hj'
  -- `η_{0j} − η_{0j'} = τ_S(β_{j'}) − τ_S(β_j)` from the two `Γ`-identities.
  have hkey : hyp.eta ⟨0, hyp.q_prime.pos⟩ j - hyp.eta ⟨0, hyp.q_prime.pos⟩ j'
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
          ((hyp.dadeHypS0 _hG).fullDadeIsometryData)
          (betaGrid hyp j')
        - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
          ((hyp.dadeHypS0 _hG).fullDadeIsometryData)
          (betaGrid hyp j) := by
    have h3 := h1.trans h2.symm
    rw [← sub_eq_zero] at h3 ⊢
    rw [← h3]
    abel
  rw [hkey, ClassFunction.inner_sub_right,
    ClassFunction.inner_eq_zero_of_disjoint_support
      (typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1
        typeISetup φ _hφ _hdeg j' hj'),
    ClassFunction.inner_eq_zero_of_disjoint_support
      (typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1
        typeISetup φ _hφ _hdeg j hj),
    sub_zero]

/-- **(13.19.c), first clause (row form)**: `(β_L^τ, η_{0j})` is independent of `j ≥ 1` — by
(13.18.c) `j`-independence (`gammaGrid_defGamma`), `η_{0j} − η_{0j'} = τ_S(β_{j'}) − τ_S(β_j)`,
and (13.19.a) support disjointness kills both `(β_L^τ, τ_S(β_·))` terms
(`typeIBetaL_inner_eta_row_sub_eq_zero`). -/
theorem typeIBetaL_eta_row_constant_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
        ClassFunction.inner (typeIBetaL typeISetup φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
          = ClassFunction.inner (typeIBetaL typeISetup φ)
              (hyp.eta ⟨0, hyp.q_prime.pos⟩ j') := by
  intro _ _ j j' hj hj'
  rw [← sub_eq_zero, ← ClassFunction.inner_sub_right]
  have h := typeIBetaL_inner_eta_row_sub_eq_zero_of_c_eq_one _hG hnoV hyp hc1
    typeISetup φ _hφ _hdeg j j' hj hj'
  convert h using 2
  exact Subsingleton.elim _ _

/-- **(13.19.c), first clause (column form)**: the S↔T-swapped row constancy — the
`typeIBetaL_eta_row_constant` instance at `hyp.swap` (Coq's re-instantiation of the section
with the pair roles interchanged).  The swap's `η`-grid is the transpose, so its row-`0`
constancy *is* the column constancy of `hyp.eta`; `β_L^τ` is `hyp`-independent, so no
transport is needed on the left argument.  The reconciled `TypePData T` comes from
`reconciled_typePData_T`, the ν-side grid supply is the explicit `pins` parameter (issue
9096 / 0118 b-5: the canonical `S16.Hypothesis.nuGridSupply` carrier at the Section-16
consumers), and the swap's structural `IsMulCommutative ↥V` input is supplied by the
unconditional symmetric non-type-I construction. -/
theorem typeIBetaL_eta_col_constant_of_d_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hd1 : hyp.d = 1)
    (pins : NuGridSupplyData hyp)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
        ClassFunction.inner (typeIBetaL typeISetup φ) (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
          = ClassFunction.inner (typeIBetaL typeISetup φ)
              (hyp.eta i' ⟨0, hyp.p_prime.pos⟩) := by
  intro _ _ i i' hi hi'
  classical
  obtain ⟨Tdata, hU, hW1, hW2⟩ := reconciled_typePData_T _hG hyp
  have hV : IsMulCommutative ↥hyp.V := hyp.isMulCommutative_V_unconditional _hG
  have hc1swap : (hyp.swap hV Tdata hU hW1 hW2 pins).c = 1 := by
    change hyp.d = 1
    exact hd1
  exact typeIBetaL_eta_row_constant_of_c_eq_one _hG hnoV
    (hyp.swap hV Tdata hU hW1 hW2 pins)
    hc1swap
    typeISetup φ _hφ _hdeg i i' hi hi'

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) T-side dichotomy** (S↔T swapped): the `typeI_caseC_dichotomy` instance at
`hyp.swap` — the swap's `tauSbetaGrid` is definitionally `tauTbetaGrid` (both are the
`'A0(T)`-Dade image of `Ind_{QW₂}^T 1 − ν_{10}`), its `u/q` are `v/p`, and its `η`-row-`0`
axis is the `η`-column-`0` axis.  Requires the `Tdata` reconciliations (supplied by the
producer from `reconciled_typePData_T`), so the swap's `A₀(T)`-carrier matches the one in
`tauTbetaGrid`'s statement.  The swap's structural input `IsMulCommutative ↥V` (13.2.a at `T`)
and its type-`P` input are both available unconditionally from the symmetric `T_nonI` carrier. -/
theorem typeI_caseC_dual_dichotomy_of_d_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hd1 : hyp.d = 1)
    (Tdata : TypePData hyp.T)
    (hU : Tdata.U = hyp.V) (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ dataL.typeIHyp.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ))
    (pins : NuGridSupplyData hyp) :
    (OddIntegerInner (tauTbetaGrid _hG hyp (hyp.T_isTypeP _hG) Tdata)
        (dataL.coh.extension φ) ∧
      (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
          / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))) ∨
      ((∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner (typeIBetaL dataL.typeIHyp φ) (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧
        hyp.q ≤ ((maxNilpotentNormalHall L).subgroupOf L).index) := by
  let hV : IsMulCommutative ↥hyp.V := hyp.isMulCommutative_V_unconditional _hG
  have hc1swap : (hyp.swap hV Tdata hU hW1 hW2 pins).c = 1 := by
    change hyp.d = 1
    exact hd1
  exact typeI_caseC_dichotomy_of_c_eq_one _hG hnoV
    (hyp.swap hV Tdata hU hW1 hW2 pins) hc1swap dataL φ _hφ _hdeg

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §13 producer for Peterfalvi (13.19).**  The Tier-A structure — `e = [L:H]`
(definitionally), the family `𝓛 = dataL.typeIHyp.Sset`, a chosen degree-`e` member `φ`
(`exists_Sset_apply_one_eq_index`), and the bridge images `β_L = typeIBetaL`,
`β_S = tauSbetaGrid`, `β_T = tauTbetaGrid` — is genuinely constructed; the (13.19.a)/(13.19.b)
facts are **proven** (`typeIBetaL_betaS_disjoint_support`,
`coherent_extension_orthogonal_eta_of_mem_Sset`); the remaining deep (13.19.c) facts are the
isolated `φ`-parametric obligations above, consumed field-by-field. -/
noncomputable def typeIOrthogonalityGridData_of_coherent78_of_c_eq_one_and_d_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) (hd1 : hyp.d = 1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (pins : NuGridSupplyData hyp) :
    TypeIOrthogonalityGridData hyp dataL :=
  { e := ((maxNilpotentNormalHall L).subgroupOf L).index
    e_eq_index := rfl
    Lset := dataL.typeIHyp.Sset
    phi := Classical.choose (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)
    phi_mem := (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
    phi_degree_eq_e :=
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
    betaL := typeIBetaL dataL.typeIHyp
      (Classical.choose (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp))
    betaS := tauSbetaGrid _hG hyp
    betaT := tauTbetaGrid _hG hyp (hyp.T_isTypeP _hG)
      (Classical.choose (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp))
    disjoint_support := typeIBetaL_betaS_disjoint_support_of_c_eq_one
      _hG hnoV hyp hc1 dataL.typeIHyp _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
    betaL_eq := typeIBetaL_eq_tau_induce_sub dataL.typeIHyp _
    Ltau_orthogonal_eta := coherent_extension_orthogonal_eta_of_mem_Sset _hG hnoV hyp dataL _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
    betaL_eta0_row_constant := typeIBetaL_eta_row_constant_of_c_eq_one
      _hG hnoV hyp hc1 dataL.typeIHyp _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
    betaL_eta0_col_constant := typeIBetaL_eta_col_constant_of_d_eq_one
      _hG hnoV hyp hd1 pins
      dataL.typeIHyp _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
    caseC := typeI_caseC_dichotomy_of_c_eq_one _hG hnoV hyp hc1 dataL _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
    caseC_dual := typeI_caseC_dual_dichotomy_of_d_eq_one _hG hnoV hyp hd1
      (Classical.choose (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp))
      (Classical.choose_spec (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp)).1
      (Classical.choose_spec (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp)).2.1
      (Classical.choose_spec (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp)).2.2
      dataL _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
      (pins := pins) }

end OddOrder.Peterfalvi.S15

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

/-- **Peterfalvi (13.13), Core form**: Clifford case (9.7.a) forces the sharp parameters,
with (13.10) supplied by the Core character-degree analysis. -/
theorem CharacterDegreeCore.caseA_parameters_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp)
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief)) :
    hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  exact caseA_parameters_of_analytic_inequality hG hyp
    (core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm pins) caseA

/-- **Peterfalvi (13.15), Core form**: Clifford case (9.7.b) determines the Singer
cyclotomic order of `u`, with (13.10) supplied by the Core character-degree analysis. -/
theorem CharacterDegreeCore.caseB_order_u_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp)
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief)) :
    (hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
      (¬ hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  exact caseB_order_u_of_analytic_inequality hG hyp
    (core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm pins) caseB

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

/-- **Peterfalvi (13.13), honest Clifford-case form**: an actual case-(9.7.a)
certificate supplies its own λ-witness, so the Core analytic relayer gives the sharp
parameters without the legacy monolithic character-degree carrier. -/
theorem Hypothesis.caseA_parameters_of_clifford_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (pins : NuGridSupplyData hyp) :
    hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := lambdaWitness_of_caseA hG hyp chief caseA
  obtain ⟨lam⟩ := hyp.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core lam pins
  have hQcomm : IsMulCommutative ↥hyp.Q :=
    IsMulCommutative.of_comm (hyp.Q_elementaryAbelian hG).comm
  exact core.caseA_parameters_of_caseB_facts hG lam hD hv hQcomm pins caseA

/-- **Peterfalvi (13.15), honest λ-dichotomy form**: an actual Clifford case-(9.7.b)
certificate has the two Singer-order alternatives without using the legacy character-degree
carrier.  In the λ-branch the Core analytic relayer proves (13.15).  In the no-λ Galois branch
`u` already has the full Singer order; the `p ≡ 1 (mod q)` alternative is impossible because
that congruence makes `q` divide the Singer quotient while the Frobenius congruence
`u ≡ 1 (mod q)` gives `q ∤ u`. -/
theorem Hypothesis.caseB_order_u_of_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief))
    (pins : NuGridSupplyData hyp) :
    (hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
      (¬ hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  have hq_not_dvd_u : ¬ hyp.q ∣ hyp.u := by
    intro hqu
    have hmod : hyp.u % hyp.q = 1 % hyp.q := hyp.u_modEq_one hG
    obtain ⟨k, hk⟩ := hqu
    have hq2 : 2 ≤ hyp.q := hyp.q_prime.two_le
    have h1q : 1 % hyp.q = 1 := Nat.one_mod_eq_one.mpr (by omega)
    rw [hk, Nat.mul_mod_right, h1q] at hmod
    omega
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  rcases lambdaCluster_or_caseB hG hyp with hlam | ⟨_hCbot, hufull⟩
  · obtain ⟨lam⟩ := hlam
    obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core lam pins
    have hQcomm : IsMulCommutative ↥hyp.Q :=
      IsMulCommutative.of_comm (hyp.Q_elementaryAbelian hG).comm
    exact core.caseB_order_u_of_caseB_facts hG lam hD hv hQcomm pins caseB
  · refine ⟨?_, fun _ => hufull⟩
    intro hmod
    have hqdvd : hyp.q ∣ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) :=
      cyclotomic_quotient_dvd_of_modEq_one hyp.p_prime hmod
    have hqu : hyp.q ∣ hyp.u := by rwa [hufull]
    exact (hq_not_dvd_u hqu).elim

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

/-- **Peterfalvi (14.4)**: case (9.7.b) holds for `T`, and `v = (q^p - 1) / (q - 1)`.  The numeric
content (`D = ⊥`, `v` full) is the named §13 obligation `T_side_caseB_facts`; the case-(9.7.b)
proposition is carried trivially (no consumer reads it). -/
theorem caseB_for_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧
        hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) :=
  ⟨⟨True, trivial, (T_side_caseB_facts _hG hyp).1, (T_side_caseB_facts _hG hyp).2⟩,
    trivial, (T_side_caseB_facts _hG hyp).2⟩

namespace CaseBForSData

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
`p ≡ 1 mod q` branch gives the divided cyclotomic value of `u`. -/
theorem u_eq_of_p_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) :=
  data.order_u_eq_of_p_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
non-`p ≡ 1 mod q` branch gives the full cyclotomic value of `u`. -/
theorem u_eq_of_not_modEq_one {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  data.order_u_eq_of_not_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, `u` is at
most the full cyclotomic quotient.  The `p ≡ 1 mod q` branch divides that
quotient by the additional factor `q`; the other branch is equality. -/
theorem u_le_full_cyclotomic {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · rw [data.u_eq_of_p_modEq_one hmod]
    have hp1_pos : 0 < hyp.base.p - 1 := by
      have hp2 : 2 ≤ hyp.base.p := hyp.base.p_prime.two_le
      omega
    have hden_le : hyp.base.p - 1 ≤ hyp.base.q * (hyp.base.p - 1) := by
      have hqpos : 1 ≤ hyp.base.q := hyp.base.q_prime.one_le
      nlinarith [Nat.mul_le_mul_right (hyp.base.p - 1) hqpos]
    exact Nat.div_le_div_left hden_le hp1_pos
  · rw [data.u_eq_of_not_modEq_one hmod]

end CaseBForSData

/-- **Peterfalvi (14.6)**: case (9.7.b) holds for `S`.

The Clifford dichotomy supplies either case (9.7.a) or an actual `CliffordCaseBData`
certificate.  The case-A branch is impossible by the completed type-I-over-normalizer
contradiction, using the `(13.13)` parameters and `c = 1`.  In the remaining branch,
the Core λ-dichotomy order endpoint supplies the two alternatives for `u`; the qualitative field
stores the genuine nonempty case-B certificate rather than an opaque compatibility proposition. -/
theorem caseB_for_S [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) :
    ∃ data : CaseBForSData hyp, data.caseB_formula := by
  classical
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData _hG
      (hyp.base.toTypesIIIIIIVSetupS _hG)
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy _hG
      (hyp.base.mkSection11CharacterDataS _hG chief) with hA | hB
  · obtain ⟨caseA⟩ := hA
    obtain ⟨hq, hu⟩ := hyp.base.caseA_parameters_of_clifford_caseA
      _hG caseA (pins := hyp.nuGridSupply)
    exact (OddOrder.Peterfalvi.S15.caseA_false_of_parameters_and_typeIOverNormalizerData
      _hG hyp.base caseA
        (hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply) hq hu
      Ldata.typeI_data).elim
  · obtain ⟨caseB⟩ := hB
    let caseB_formula : Prop := Nonempty
      (OddOrder.Peterfalvi.S11.CliffordCaseBData
        (hyp.base.mkSection11CharacterDataS _hG chief))
    have hcaseB : caseB_formula := ⟨caseB⟩
    obtain ⟨hu_mod, hu_not_mod⟩ :=
      hyp.base.caseB_order_u_of_lambda_dichotomy
        _hG caseB (pins := hyp.nuGridSupply)
    exact ⟨⟨caseB_formula, hcaseB, hu_mod, hu_not_mod, True, trivial⟩, hcaseB⟩

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- Arithmetic bridge for **Peterfalvi (14.8)**: under the Section 16 prime
ordering `q < p`, the T-side full cyclotomic quotient gives a strictly larger
`(v - 1) / p` ratio than the S-side full cyclotomic quotient gives for
`(u - 1) / q`. -/
theorem key_ratio_inequality_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) :
    (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  have hratio := cyclotomic_ratio_gt_of_q_lt_p
    hyp.base.p_prime hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p
  have hqpos : (0 : ℚ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hu_sub : ((hyp.base.u - 1 : ℕ) : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le_sub_right Sdata.u_le_full_cyclotomic 1
  have hu_div : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) /
        (hyp.base.q : ℚ) :=
    div_le_div_of_nonneg_right hu_sub (le_of_lt hqpos)
  rw [Tdata.v_eq]
  exact lt_of_le_of_lt hu_div hratio

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (13.19.b), the `η`-grid orthogonality of *every* coherent image `ζ_k^ν`**
(the Coq `o_tauLeta` for the whole family, not just the distinguished index).  For any family
member `k ≠ ind1H`, the coherent image `ζ_k^ν = (dataM.h78 hG).nu (ζ_k)` is orthogonal to the
entire `η`-grid.  Identical (3.6)–(3.8)/(13.19.b) engine as `caseB_eta_orthogonal_psi`, but with
the distinguished index `zetaDistinct` replaced by an arbitrary `k`: `ζ_k^ν` has unit norm
(`nu_zeta_norm_one`), its conjugate partner `ζ_{k'}^ν` (`exists_conjIndex_at`, generic in the
index) is a distinct unit-norm virtual character (`nu_zeta_inner_nu_conj_eq_zero`), and the
conjugate difference `ζ_k^ν − ζ_{k'}^ν` (supported in `Ã(M)`, `nu_zeta_sub_conj_support_at`,
also generic) vanishes on `Ŵ^G` by the same (13.19.a) Dade-support avoidance `hDadeAvoid`. -/
theorem caseB_eta_orthogonal_nu_zeta_at [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (dataM : TypeICoherent78Data M)
    (hDadeAvoid : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport)
    {k : Fin (dataM.n + 1)} (hk : k ≠ (dataM.h78 hG).ind1H) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j)
        ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)) = 0 := by
  classical
  -- the kernel-index datum for `k` and its conjugate partner `k'`
  have hkne : k ≠ dataM.ind1H := by rwa [dataM.h78_ind1H_eq] at hk
  obtain ⟨k', hk'_ne, hk'⟩ := dataM.exists_conjIndex_at hG hkne
  -- engine inputs from the coherence bundle
  have hpsiZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k) ∈ ZIrr G := by
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hkne))
  have hconjZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k') ∈ ZIrr G := by
    have hk'ne_data : k' ≠ dataM.ind1H := by rw [← dataM.h78_ind1H_eq]; exact hk'_ne
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hk'ne_data))
  have hpsi1 := dataM.nu_zeta_norm_one hG hk
  have hconj1 := dataM.nu_zeta_norm_one hG hk'_ne
  have hcross := dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hkne hk'_ne hk'
  have hsupp := dataM.nu_zeta_sub_conj_support_at hG hkne hk'_ne hk'
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k')) x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx (hsupp (ClassFunction.mem_support.mpr hval))
  exact eta_orthogonal_of_norm_one_pair_vanish hyp hpsiZ hconjZ hpsi1 hconj1 hcross hvanish

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace MHypothesis

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

/-- The distinguished member belongs to the coherent source family. -/
theorem psi_mem [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.psi ∈ Mdata.Mset := by
  exact Mdata.coherent78.zeta_mem_Sset (Ne.symm Mdata.coherent78.ind1H_ne_zero)

theorem h78_H_eq [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.h78.hyp76.H = Mdata.K := by
  calc Mdata.h78.hyp76.H = Mdata.coherent78.kernel :=
        Mdata.coherent78.h78_H_eq Mdata.hG
    _ = maxNilpotentNormalHall Mdata.M := Mdata.typeIHyp.typeI.typeF.H_eq
    _ = Mdata.K := Mdata.K_eq_MF.symm

/-- The complement index of the canonical (7.8) bundle is the concrete index `e = |M : K|`
carried by `MHypothesis`. -/
theorem h78_complementIndex_eq_e [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) : Mdata.h78.complementIndex = Mdata.e := by
  have hKleM : Mdata.K ≤ Mdata.M :=
    Mdata.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le Mdata.M
  have hko : Mdata.h78.kernelOrder = Mdata.k := by
    rw [Mdata.k_eq_card_K]
    change Nat.card ↥(Mdata.h78.hyp76.H) = Nat.card ↥Mdata.K
    rw [Mdata.h78_H_eq]
  have hmul := Mdata.h78.kernelOrder_mul_complementIndex_eq_card_L
  rw [hko, Mdata.k_eq_card_K] at hmul
  have hcardK : Nat.card ↥(Mdata.K.subgroupOf Mdata.M) = Nat.card ↥Mdata.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
  have hidx : Nat.card ↥Mdata.K * (Mdata.K.subgroupOf Mdata.M).index = Nat.card ↥Mdata.M := by
    rw [← hcardK]
    exact Subgroup.card_mul_index _
  rw [← Mdata.e_eq_index] at hidx
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hmul.trans hidx.symm)

end MHypothesis

/-- **Peterfalvi (13.17.c), V-side dual complement alternatives**:
`e = |M : K| = p` or `e = p q`.

The alternatives are supplied by lane b's corrected `exists_M_structural_dichotomy` and stored
faithfully on the (14.10) witness. -/
theorem MHypothesis.complementIndex_eq_p_or_pq [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    Mdata.e = hyp.base.p ∨ Mdata.e = hyp.base.p * hyp.base.q := by
  exact Mdata.complementIndex_cases

/-- **Peterfalvi (13.17.c), V-side dual input for (14.11.1)**:
`e = |M : K| ≤ p q`, without choosing the `p q` branch. -/
theorem MHypothesis.complementIndex_le_pq [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    Mdata.e ≤ hyp.base.p * hyp.base.q := by
  rcases Mdata.complementIndex_eq_p_or_pq _hG with he | he
  · rw [he]
    exact Nat.le_mul_of_pos_right _ hyp.base.q_prime.pos
  · exact he.le

/-- **Peterfalvi (14.11.1)**: if `K != V`, then `k` is large and the first quotient is
strictly greater than `(v - 1) / p`.

The third conjunct `(v − 1) / p > (u − 1) / q` is now a genuine proof: it is the arithmetic
ratio comparison `key_ratio_inequality_of_caseB_data` (14.8), fed by the (14.4)/(14.6) case-(9.7.b)
cyclotomic data.  The two structural bounds remain the named §13/§14 obligation
`main_size_bounds_structural`. -/
theorem main_size_bounds [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hnoV hncH0C hyp
  obtain ⟨Tdata, _⟩ := caseB_for_T _hG hyp
  obtain ⟨Sdata, _⟩ := caseB_for_S _hG hyp Ldata
  obtain ⟨hk, hke⟩ :=
    main_size_bounds_structural _hG hnoV hncH0C hyp Mdata hne (Mdata.complementIndex_le_pq _hG)
  exact ⟨hk, hke, key_ratio_inequality_of_caseB_data Tdata Sdata⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19), synchronized M-side grid source.**

The explicit `TypeIOrthogonalityGridData` producer
`typeIOrthogonalityGridData_of_coherent78_of_c_eq_one_and_d_eq_one`
(Pf (13.19), landed 2026-07-12) now fixes the family `Lset := dataL.typeIHyp.Sset` and chooses the
distinguished degree-`e` member via `exists_Sset_apply_one_eq_index`, so its `phi_mem` **is** the
required `phi ∈ typeIHyp.Sset` membership.  This theorem therefore just instantiates that producer
at `Mdata.coherent78` (using the symmetric non-type-I carrier for its T-side inputs) and
projects the chosen member's membership; no false uniqueness of the two class functions is
required. -/
theorem exists_betaMGridData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (_hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    ∃ grid : OddOrder.Peterfalvi.S15.TypeIOrthogonalityGridData hyp.base Mdata.coherent78,
      grid.phi ∈ Mdata.typeIHyp.Sset := by
  -- The faithful explicit (13.19) producer now fixes
  -- `Lset := dataL.typeIHyp.Sset` with `phi := choose (exists_Sset_apply_one_eq_index …)`, so the
  -- chosen member is *in* `Sset` by construction.  The producer uses the symmetric
  -- non-type-I carrier for its T-side type-`P` and commutativity inputs.
  have hc1 : hyp.base.c = 1 :=
    hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply
  have hDbot : hyp.base.D = ⊥ := (T_side_caseB_facts _hG hyp).1
  have hd1 : hyp.base.d = 1 := by
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  exact ⟨OddOrder.Peterfalvi.S15.typeIOrthogonalityGridData_of_coherent78_of_c_eq_one_and_d_eq_one
      _hG hnoV hyp.base hc1 hd1 Mdata.coherent78 (pins := hyp.nuGridSupply),
    (Classical.choose_spec (OddOrder.Peterfalvi.S15.exists_Sset_apply_one_eq_index _hG hnoV
      Mdata.coherent78.typeIHyp)).1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), faithful M-side source adapter.**  Projects the corrected conjunction
alternatives supplied by lane b.  The choice-invariance theorem identifies the `eta` coefficients
of its `β_L^τ` with those of the actual `Mdata.betaM`; it does not overclaim equality of the two
class functions. -/
theorem betaMGridParityAlternatives [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    BetaMGridParityAlternatives hyp Mdata := by
  obtain ⟨grid, hphi⟩ := exists_betaMGridData _hG hnoV hncH0C hyp Mdata
  have hbeta : Mdata.betaM =
      OrthogonalitySwitchData.coherentBeta _hG Mdata.coherent78 := rfl
  have hcoeff : ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
        ClassFunction.inner grid.betaL (hyp.base.eta i j) =
          ClassFunction.inner Mdata.betaM (hyp.base.eta i j) := by
    intro _ _ i j
    rw [hbeta]
    exact OrthogonalitySwitchData.typeIGrid_betaL_inner_eta_eq_h78_beta
      _hG hnoV hncH0C Mdata.M_maximal Mdata.coherent78 grid hphi i j
  have heM : Mdata.e = ((maxNilpotentNormalHall Mdata.M).subgroupOf Mdata.M).index := by
    rw [Mdata.e_eq_index, Mdata.K_eq_MF]
  have he : grid.e = Mdata.e := grid.e_eq_index.symm.trans heM.symm
  have hH : Mdata.typeIHyp.H = Mdata.K := by
    rw [OddOrder.Peterfalvi.S14.Hypothesis.H, Mdata.typeIHyp.typeI.typeF.H_eq,
      Mdata.K_eq_MF]
  have hk : Nat.card ↥Mdata.typeIHyp.H = Mdata.k := by
    rw [hH, ← Mdata.k_eq_card_K]
  constructor
  · rcases grid.caseC with hbound | hodd
    · left
      have h := hbound.2
      rw [hk, he] at h
      exact h
    · right
      intro j hj
      obtain ⟨n, hn, hinner⟩ := hodd.1 j hj
      refine ⟨n, hn, ?_⟩
      intro _ _
      calc
        ClassFunction.inner Mdata.betaM
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) =
            ClassFunction.inner grid.betaL
              (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) :=
          (hcoeff ⟨0, hyp.base.q_prime.pos⟩ j).symm
        _ = (n : ℂ) := hinner
  · rcases grid.caseC_dual with hbound | hodd
    · left
      have h := hbound.2
      rw [hk, he] at h
      exact h
    · right
      intro i hi
      obtain ⟨n, hn, hinner⟩ := hodd.1 i hi
      refine ⟨n, hn, ?_⟩
      intro _ _
      calc
        ClassFunction.inner Mdata.betaM
            (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩) =
            ClassFunction.inner grid.betaL
              (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩) :=
          (hcoeff i ⟨0, hyp.base.p_prime.pos⟩).symm
        _ = (n : ℂ) := hinner

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.1) → (13.19.c)**: the two strict size gaps exclude both degree-bound
branches of (13.19.c), so the row and column coefficients of the actual `β_M^τ` are odd. -/
theorem betaM_axis_odd_of_main_size_bounds [Finite G]
    {hyp : Hypothesis (G := G)} {Mdata : MHypothesis hyp}
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (h1319 : BetaMGridParityAlternatives hyp Mdata) :
    (∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
      OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
        (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)) ∧
    (∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
      OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
        (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) := by
  constructor
  · rcases h1319.row with hbound | hodd
    · exfalso
      linarith [hsize.2.1, hsize.2.2]
    · exact hodd
  · rcases h1319.col with hbound | hodd
    · exfalso
      linarith [hsize.2.1]
    · exact hodd

/-- **Faithful §7/§3 Dade carrier for the `β_M` expansion of Peterfalvi (14.11.2).**

This is the `M`-instance of the (7.8) Dade-coherence decomposition specialised to the `η`-grid,
isolating the genuine character-theoretic content of (14.11.2) away from the pure algebra:

* `betaM_seven_eight` — **Peterfalvi (7.8.a)** for `M`: `β_M^τ = 1_G − χ + Δ`, the Dade-isometry
  image of `β_M = Ind_K^M 1_K − ψ` decomposed against the principal character `1_G` and the removed
  unit-norm coherent image `χ` (`= ψ^{τ₁}` or `−ψ̄^{τ₁}`, recorded by `chi_classification`;
  `chi_norm` is its branch-independent consequence).  In the `χ = ψ^{τ₁} = ζ^ν` branch this is the
  `M`-instance
  of `S09.Hypothesis78.beta_eq_constOne_sub_zetaImage_add_delta` (`β = 1_G − ζ^ν + Δ`); see the
  bridge lemma `betaMExpansionData_of_hypothesis78` below.
* `grid_eq` — **Peterfalvi (13.1.d)/(7.8.b)** `η`-grid identification: `1_G + Δ = Σ_{ij} ε_ij η_ij`.
  The principal `η₀₀` carries the `1_G`, the off-principal grid realizes the residual `Δ`, and the
  `±1` signs come from the Dade congruence `a_ij ≡ 1 (mod 2)` (13.19.c / 7.8.c) with
  `Σ a_ij² ≤ e − 1` and `e = p q` (`all_pm_one_and_card_of_odd_sq_sum_le`).

All fields are the conditional conclusion of the (14.11.2) support-coherence argument: besides
the §3/§4/§5 Dade machinery it uses coefficient projection, norm tightness, and residual
vanishing.  Cf. `EtaGenericData` for the dual generic-set carrier. -/
structure BetaMExpansionData [Finite G]
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  /-- The equality `e = p q`, obtained in the same norm-collapse as the signed expansion. -/
  e_eq_pq : Mdata.e = hyp.base.p * hyp.base.q
  /-- The residual `Δ` of the (7.8.a) Dade expansion `β_M = 1_G − χ + Δ`. -/
  delta : ClassFunction G ℂ
  /-- The removed unit-norm character `χ` (`= ψ^{τ₁}` or `−ψ̄^{τ₁}`). -/
  chi : ClassFunction G ℂ
  /-- `χ` has the same pointwise absolute value as `ψ^{τ₁}` (holds for both branches, since
  `|z| = |z̄|`) — exactly what (14.11.3) consumes. -/
  chi_norm : ∀ g : G, ‖chi g‖ = ‖(Mdata.tau1 Mdata.psi) g‖
  /-- **Peterfalvi (14.11.2)**: the removed character is the coherent image of `ψ`, or the
  negative coherent image of its complex conjugate. -/
  chi_classification :
    chi = Mdata.tau1 Mdata.psi ∨ chi = -(Mdata.tau1 Mdata.psi.conj)
  /-- **Peterfalvi (7.8.a)** for `M`: `β_M^τ = 1_G − χ + Δ`. -/
  betaM_seven_eight :
    Mdata.betaM = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G - chi + delta
  /-- The `±1` signs of the `η`-grid expansion. -/
  signs : Fin hyp.base.q → Fin hyp.base.p → ℤ
  signs_pm_one : ∀ i j, signs i j = 1 ∨ signs i j = -1
  /-- **Peterfalvi (13.1.d)/(7.8.b)** `η`-grid identification: `1_G + Δ = Σ_{ij} ε_ij η_ij`. -/
  grid_eq :
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + delta =
      ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Faithful conditional support-coherence producer for (14.11.2).**  Under `K ≠ V`, the
coefficient projection and norm-tightness argument derives `e = p q`, vanishing of the orthogonal
residual, the signed `η`-grid expansion, and the classification of `χ`.  The bridge lemma
`betaMExpansionData_of_hypothesis78` supplies its concrete (7.8.a) branch. -/
noncomputable def betaM_expansion_data [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (_hne : Mdata.K ≠ hyp.base.V)
    (_he_le : Mdata.e ≤ hyp.base.p * hyp.base.q)
    (_hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (_hrow : ∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
      OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
        (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j))
    (_hcol : ∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
      OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
        (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) :
    BetaMExpansionData hyp Mdata := by
  classical
  haveI := Mdata.coherent78.kernelIn_normal
  set H78 := Mdata.h78 with hH78
  set BD := Mdata.coherent78.betaDecomp Mdata.hG with hBD
  -- The Fourier coefficients of `β_M` on the `η`-grid are integers.
  have hbetaZ : Mdata.betaM ∈ ZIrr G := by
    exact H78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (Mdata.coherent78.h78_ind_mem_ZIrr Mdata.hG)
      (Mdata.coherent78.h78_zeta_irreducible Mdata.hG)
  have hint : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ∃ n : ℤ, ClassFunction.inner Mdata.betaM (hyp.base.eta i j) = (n : ℂ) :=
    fun i j => ClassFunction.inner_mem_ZIrr_int hbetaZ (eta_mem_ZIrr hyp.base i j)
  choose m hcoeff using hint
  -- Every coherent family image, hence also the weighted sum, is orthogonal to the grid.
  have hDadeAvoid :=
    OrthogonalitySwitchData.mSide_dadeSupport_avoids_regular
      (hyp := hyp) Mdata.hG hnoV hncH0C Mdata.M_maximal Mdata.coherent78
  have hetaNu : ∀ (k : Fin (Mdata.coherent78.n + 1)), k ≠ H78.ind1H →
      ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
        ClassFunction.inner (H78.nu (H78.hyp76.zeta k)) (hyp.base.eta i j) = 0 := by
    intro k hk i j
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      OrthogonalitySwitchData.caseB_eta_orthogonal_nu_zeta_at
        Mdata.hG hyp.base Mdata.coherent78 hDadeAvoid hk i j,
      star_zero]
  have hWeta : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner H78.weightedNuSum (hyp.base.eta i j) = 0 := by
    intro i j
    rw [show H78.weightedNuSum =
        ∑ k ∈ (Finset.univ.erase H78.ind1H),
          (H78.hyp76.zeta k (1 : ↥Mdata.M) /
            (H78.hyp76.zeta H78.zetaDistinct (1 : ↥Mdata.M) *
              ClassFunction.inner (H78.hyp76.zeta k) (H78.hyp76.zeta k))) •
            H78.nu (H78.hyp76.zeta k) from rfl]
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [ClassFunction.inner_smul_left, hetaNu k (Finset.mem_erase.mp hk).1 i j, mul_zero]
  -- Consequently the grid projection of `β_M` is the projection of `1_G + Γ`.
  set phi : ClassFunction G ℂ :=
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + BD.Gamma with hphi
  have hphi_coeff : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner phi (hyp.base.eta i j) = (m i j : ℂ) := by
    intro i j
    rw [← hcoeff i j, hphi,
      show Mdata.betaM = H78.beta by rw [hH78],
      show H78.beta = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          - H78.nu (H78.hyp76.zeta H78.zetaDistinct)
          + (BD.a : ℂ) • H78.weightedNuSum + BD.Gamma from BD.beta_eq]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left,
      hetaNu H78.zetaDistinct H78.zetaDistinct_ne_ind1H i j, hWeta i j, mul_zero,
      sub_zero, add_zero]
  -- The principal coefficient is one.
  have heta0 : hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ =
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne G := by
    rw [eta_principal_eq_trivial hyp.base]
    exact ClassFunction.ext fun _ => rfl
  have hprincipalInner : ClassFunction.inner Mdata.betaM
      (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩) = 1 := by
    rw [heta0, show Mdata.betaM = H78.beta by rw [hH78],
      H78.beta_eq_constOne_sub_zetaImage_add_delta,
      ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one,
      BD.orth_one H78.zetaDistinct H78.zetaDistinct_ne_ind1H,
      H78.delta_orth_one BD]
    ring
  have hprincipal : m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1 := by
    have hm := hcoeff ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩
    have hc : ((m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ : ℤ) : ℂ) = 1 :=
      hm.symm.trans hprincipalInner
    exact_mod_cast hc
  -- Support avoidance gives the four-corner relation (3.7).
  have hbetaVanish : ∀ x ∈ conjClassSet
      ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      Mdata.betaM x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx
      (H78.beta_support_subset_dadeSupport (ClassFunction.mem_support.mpr hval))
  have hrelation : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      m i j + m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ =
        m i ⟨0, hyp.base.p_prime.pos⟩ + m ⟨0, hyp.base.q_prime.pos⟩ j := by
    intro i j
    have h := inner_eta_grid_relation hyp.base hbetaVanish i j
    rw [hcoeff i j,
      hcoeff ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩,
      hcoeff i ⟨0, hyp.base.p_prime.pos⟩,
      hcoeff ⟨0, hyp.base.q_prime.pos⟩ j] at h
    exact_mod_cast h
  -- The selected (13.19.c) alternatives make the two non-principal axes odd.
  have hrow : ∀ j, j ≠ ⟨0, hyp.base.p_prime.pos⟩ →
      Odd (m ⟨0, hyp.base.q_prime.pos⟩ j) := by
    intro j hj
    have hjnat : (j : ℕ) ≠ 0 := by
      intro hj0
      apply hj
      apply Fin.ext
      exact hj0
    obtain ⟨n, hnodd, hn⟩ := _hrow j hjnat
    have hnval : ClassFunction.inner Mdata.betaM
        (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) = (n : ℂ) := hn
    have hcast : ((m ⟨0, hyp.base.q_prime.pos⟩ j : ℤ) : ℂ) = (n : ℂ) :=
      (hcoeff ⟨0, hyp.base.q_prime.pos⟩ j).symm.trans hnval
    have hmn : m ⟨0, hyp.base.q_prime.pos⟩ j = n := by exact_mod_cast hcast
    rwa [hmn]
  have hcol : ∀ i, i ≠ ⟨0, hyp.base.q_prime.pos⟩ →
      Odd (m i ⟨0, hyp.base.p_prime.pos⟩) := by
    intro i hi
    have hinat : (i : ℕ) ≠ 0 := by
      intro hi0
      apply hi
      apply Fin.ext
      exact hi0
    obtain ⟨n, hnodd, hn⟩ := _hcol i hinat
    have hnval : ClassFunction.inner Mdata.betaM
        (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩) = (n : ℂ) := hn
    have hcast : ((m i ⟨0, hyp.base.p_prime.pos⟩ : ℤ) : ℂ) = (n : ℂ) :=
      (hcoeff i ⟨0, hyp.base.p_prime.pos⟩).symm.trans hnval
    have hmn : m i ⟨0, hyp.base.p_prime.pos⟩ = n := by exact_mod_cast hcast
    rwa [hmn]
  have hecomp : H78.complementIndex = Mdata.e := by
    rw [hH78]
    exact Mdata.h78_complementIndex_eq_e
  obtain ⟨hepqH, hpm, hgrid⟩ :=
    Mdata.coherent78.etaGrid_projection_rigidity Mdata.hG hyp.base m
      (by simpa [phi, BD] using hphi_coeff) hprincipal hrelation hrow hcol (by
        rw [hecomp]
        exact _he_le)
  have hepq : Mdata.e = hyp.base.p * hyp.base.q := by
    rw [← hecomp]
    exact hepqH
  set X : ClassFunction G ℂ := etaGridProjection hyp.base m with hX
  set chi : ClassFunction G ℂ := X - Mdata.betaM with hchi
  have hchiSelf : ClassFunction.inner chi chi = 1 := by
    rw [hchi, hX, show Mdata.betaM = H78.beta by rw [hH78]]
    exact Mdata.coherent78.etaGrid_projection_sub_beta_norm_one Mdata.hG hyp.base m
      hpm hepqH (by simpa [hH78] using hcoeff)
  have hetaNuData : ∀ (k : Fin (Mdata.coherent78.n + 1)),
      k ≠ Mdata.coherent78.ind1H → ∀ i j,
        ClassFunction.inner
          ((Mdata.coherent78.h78 Mdata.hG).nu
            ((Mdata.coherent78.h78 Mdata.hG).hyp76.zeta k))
          (hyp.base.eta i j) = 0 := by
    intro k hk i j
    have hk' : k ≠ (Mdata.coherent78.h78 Mdata.hG).ind1H := by
      rw [Mdata.coherent78.h78_ind1H_eq Mdata.hG]
      exact hk
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      OrthogonalitySwitchData.caseB_eta_orthogonal_nu_zeta_at
        Mdata.hG hyp.base Mdata.coherent78 hDadeAvoid hk' i j,
      star_zero]
  have hclassSource :
      chi = Mdata.h78.nu (Mdata.h78.hyp76.zeta Mdata.h78.zetaDistinct) ∨
      chi = -Mdata.h78.nu (Mdata.h78.hyp76.zeta Mdata.h78.zetaDistinct).conj := by
    simpa [hchi, hX] using
      (Mdata.coherent78.etaGrid_projection_sub_beta_classification
        Mdata.hG hyp.base m hetaNuData (by simpa [hchi, hX, hH78] using hchiSelf))
  have hclass :
      chi = Mdata.tau1 Mdata.psi ∨ chi = -(Mdata.tau1 Mdata.psi.conj) := by
    rcases hclassSource with h | h
    · left
      exact h
    · right
      rw [Mdata.coherent78.h78_zetaDistinct_eq Mdata.hG,
        Mdata.coherent78.h78_zeta_eq Mdata.hG] at h
      exact h
  -- Both classified branches have the pointwise norm of `ψ^{τ₁}`.
  have hpsiS : Mdata.psi ∈ Mdata.typeIHyp.Sset := Mdata.psi_mem
  have h2 : ∃ psi ∈ Mdata.typeIHyp.Sset, psi ≠ Mdata.psi := by
    obtain ⟨j₁, hj₁ne, hj₁⟩ := Mdata.coherent78.exists_conjIndex Mdata.hG
    have hj₁mem : Mdata.h78.hyp76.zeta j₁ ∈ Mdata.typeIHyp.Sset :=
      Mdata.coherent78.zeta_mem_Sset (by
        rw [← Mdata.coherent78.h78_ind1H_eq Mdata.hG]
        exact hj₁ne)
    refine ⟨Mdata.h78.hyp76.zeta j₁, hj₁mem, ?_⟩
    rw [hj₁]
    exact (Mdata.coherent78.h78_zeta_ne_conj Mdata.hG Mdata.hG.odd).symm
  have hconj : (Mdata.tau1 Mdata.psi).conj = Mdata.tau1 Mdata.psi.conj :=
    Mdata.coherent78.coherence_extension_conj Mdata.hG hpsiS h2
  have hchiNorm : ∀ g : G, ‖chi g‖ = ‖(Mdata.tau1 Mdata.psi) g‖ := by
    intro g
    rcases hclass with h | h
    · rw [h]
    · rw [h, ClassFunction.neg_apply, norm_neg, ← hconj,
        ClassFunction.conj_apply, norm_star]
  refine
    { e_eq_pq := hepq
      delta := BD.Gamma
      chi := chi
      chi_norm := hchiNorm
      chi_classification := hclass
      betaM_seven_eight := ?_
      signs := m
      signs_pm_one := hpm
      grid_eq := ?_ }
  · rw [hchi, hX, show Mdata.betaM = H78.beta by rw [hH78]]
    rw [← show OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + BD.Gamma =
        etaGridProjection hyp.base m by simpa [BD] using hgrid]
    abel
  · simpa [BD, hX, etaGridProjection] using hgrid

/-- **Peterfalvi (14.11.2)**: under `K ≠ V`, `e = p q` and `β_M^τ` is a signed sum of the
`η_ij` grid with one unit-norm character `χ` removed:
`β_M^τ = Σ_{0≤i<q, 0≤j<p} (±η_ij) − χ`, where `χ = ψ^{τ₁}` or `−ψ̄^{τ₁}`.

The equality `e = p q`, coefficient rigidity, vanishing of the orthogonal residual, and the χ
classification are derived together inside `betaM_expansion_data` from `K ≠ V`, (14.11.1), the
faithful (13.17.c)-dual bound, and the explicit (13.19.c) alternatives.  This public projection
retains only the pointwise norm consequence needed downstream.  No conclusion of (14.11.2) is
read from `MHypothesis`. -/
theorem _root_.solution [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.e = hyp.base.p * hyp.base.q ∧
      ∃ ε : Fin hyp.base.q → Fin hyp.base.p → ℤ,
        (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
        ∃ χ : ClassFunction G ℂ,
          (∀ g : G, ‖χ g‖ = ‖(Mdata.tau1 Mdata.psi) g‖) ∧
          Mdata.betaM =
            (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (ε i j : ℂ) • hyp.base.eta i j) - χ := by
  have he_le := Mdata.complementIndex_le_pq _hG
  have hsize := main_size_bounds _hG hnoV hncH0C hyp Mdata hne
  have haxis :=
    betaM_axis_odd_of_main_size_bounds hsize
      (betaMGridParityAlternatives _hG hnoV hncH0C hyp Mdata)
  obtain ⟨hepq, delta, chi, hchi_norm, _hchi_classification, hbeta, signs, hsigns, hgrid⟩ :=
    betaM_expansion_data _hG hnoV hncH0C hyp Mdata hne he_le hsize haxis.1 haxis.2
  refine ⟨hepq, ?_⟩
  refine ⟨signs, hsigns, chi, hchi_norm, ?_⟩
  rw [hbeta, ← hgrid]
  abel

end OddOrder.Peterfalvi.S16
