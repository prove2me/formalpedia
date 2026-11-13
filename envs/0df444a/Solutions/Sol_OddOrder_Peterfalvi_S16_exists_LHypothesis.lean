-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.exists_LHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:20:02.889144+00:00
-- url     : https://prove2.me/submissions/b70b8dbc-ff44-4de9-9b28-9ee7c7db05be

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/TISubset.lean
--   OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean
--   OddOrder/Peterfalvi/S10_CoherenceWiring.lean
--   OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructureBasic.lean
--   OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructure.lean
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S14_MaximalI/NormPackage.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean
--   OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean
--   OddOrder/Peterfalvi/S15_SAndTDefs.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
--   OddOrder/Peterfalvi/S15_ComplementStructure.lean
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
--   OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
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
import Theorems.Thm_OddOrder_Isaacs_Ch06_IsFrobeniusGroup_conjComplement
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_S
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_analytic_inequality_of_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_sSet_irr
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_forces_T_caseB_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseB_member
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseA
import Theorems.Thm_OddOrder_Peterfalvi_S15_complement_inf_Q_eq_W1
import Theorems.Thm_OddOrder_Peterfalvi_S15_exists_typeI_maximal_overNormalizer_U
import Theorems.Thm_OddOrder_Peterfalvi_S15_complement_le_QW2_of_D_eq_bot
import Theorems.Thm_OddOrder_Peterfalvi_S15_Q_W2_structure
import Theorems.Thm_OddOrder_Peterfalvi_S15_card_LF_coprime_pq
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_tauS_mu_row0_vanish_on_V
import Theorems.Thm_OddOrder_Peterfalvi_S15_typeI_caseC_dichotomy_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_exists_mem_conj_W2_le_of_dvd_card
import Theorems.Thm_OddOrder_Peterfalvi_S15_exists_conj_typeP_U_of_coprime
import Theorems.Thm_OddOrder_Peterfalvi_S15_coprime_card_U_card_P_of_disjoint
import Theorems.Thm_OddOrder_Peterfalvi_S15_dadeSupport_betaGrid_disjoint_support_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_coherent_extension_orthogonal_eta_of_mem_Sset
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S15_c_eq_one_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S16_cyclotomic_ratio_gt_of_q_lt_p
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_side_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_ratio_le

-- ===== OddOrder/GroupTheory/TISubset.lean =====
namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

namespace IsTISubset

variable {A : Set G} {L : Subgroup G}

/-- ホスト部分群を緩めても TI: `L ≤ L'` なら `A` は `L'` 相対でも TI. -/
theorem mono {L' : Subgroup G} (hA : IsTISubset A L) (hLL' : L ≤ L') :
    IsTISubset A L' :=
  fun g hg => hLL' (hA g hg)

end IsTISubset

end OddOrder.GroupTheory

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

-- ===== OddOrder/Peterfalvi/S10_CoherenceWiring.lean =====
namespace OddOrder.Peterfalvi.CoherenceWiring

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **Peterfalvi (6.8) coherence-wiring bridge.**

Let `L` be a maximal subgroup (used here as the ambient group of the character theory) and
`H ◁ L` the kernel of its Sibley Dade setup.  Given a faithful Sibley hypothesis `sib`
(`S08.SibleyDadeHypothesis`) for `(G, L, H)` and identifications

* `htau : sib.tau = τ`   — its §4 Dade isometry is the spine's integral character map,
* `hS   : sib.S = S`      — its base family `{Ind_H^L θ}` is the spine's family,
* `hA0  : H^#(supported in L) = A₀` — its `H^#`-support is the spine's `A₀`,

the family `S` is coherent for `τ` on `A₀`.

The proof is the (6.8) capstone `S08.sibleySetup_is_coherent` transported along the three
identifications; it carries no `sorry`.  All the maximal-subgroup content is concentrated in
the `sib` witness (the §14 structure theory), exactly as in Peterfalvi's text, where (13.2.d)
etc. read off "(6.8) applies". -/
noncomputable def coherent_of_sibley {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card L : ℂ)] {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (sib : S08.SibleyDadeHypothesis G L H)
    {τ : S07.IntegralCharacterMap ↥L G} {S : Set (ClassFunction ↥L ℂ)} {A0 : Set ↥L}
    (htau : sib.tau = τ) (hS : sib.S = S)
    (hA0 : S04.supportInSubgroup (S08.sharpImage H) L = A0) :
    S07.IsCoherent τ S A0 := by
  subst htau; subst hS; subst hA0
  exact S08.sibleySetup_is_coherent sib

/-- `Nonempty`-wrapped form of `coherent_of_sibley`, for the spine riders phrased as
`Nonempty (S07.IsCoherent …)` (e.g. Peterfalvi (10.4), (13.2.d)). -/
theorem nonempty_coherent_of_sibley {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card L : ℂ)] {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (sib : S08.SibleyDadeHypothesis G L H)
    {τ : S07.IntegralCharacterMap ↥L G} {S : Set (ClassFunction ↥L ℂ)} {A0 : Set ↥L}
    (htau : sib.tau = τ) (hS : sib.S = S)
    (hA0 : S04.supportInSubgroup (S08.sharpImage H) L = A0) :
    Nonempty (S07.IsCoherent τ S A0) :=
  ⟨coherent_of_sibley sib htau hS hA0⟩

/-- Discharge an opaque coherence rider `Nonempty (S07.IsCoherent τ S A₀)` from a
`SibleyTarget` witness, via (6.8).  `sorry`-free. -/
theorem coherent_of_sibleyTarget {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card L : ℂ)] {τ : S07.IntegralCharacterMap ↥L G}
    {S : Set (ClassFunction ↥L ℂ)} {A0 : Set ↥L} (w : SibleyTarget τ S A0) :
    Nonempty (S07.IsCoherent τ S A0) :=
  letI := w.invH
  nonempty_coherent_of_sibley w.sib w.tau_eq w.S_eq w.A0_eq

end OddOrder.Peterfalvi.CoherenceWiring

-- ===== OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructureBasic.lean =====
namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Transporting a §4 Dade datum along an equality of its support set preserves the Dade isometry
`dadeIntegralCharacterMap`.**  The isometry's codomain `IntegralCharacterMap ↥L G` does not mention
the support `A`, so rewriting `A` to `A'` in the datum leaves the map unchanged (`subst` + `rfl`).
This lets the (6.8) `SibleyDadeHypothesis` (Dade datum on `sharpImage H`) carry *exactly* the (12.1)
isometry `hyp.tau` (Dade datum on `A(L)`) after the ambient identification `sharpImage H = A(L)` —
the map is an *arbitrary* linear extension off the supported lattice
(`dadeIntegralCharacterMap_apply_of_support`), so only the identical datum (transported), not a
re-construction via `of_isTISubset`, reproduces `hyp.tau`. -/
theorem dadeIntegralCharacterMap_transport_ambient {L : Subgroup G} [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {A A' : Set G} (hEq : A = A')
    (dade : OddOrder.Peterfalvi.S04.Hypothesis G A L) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hEq ▸ dade)
        ((hEq ▸ dade).fullDadeIsometryData)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap dade
        (dade.fullDadeIsometryData) := by
  subst hEq; rfl

/-- **The centralizer-support of `N^#` collapses to `N^#` for a Frobenius `L` with kernel `N`.**
The (12.1) type-I Dade support is `A(L) = centralizerSupport (N^#) L`; when `L` is a Frobenius group
with kernel `N` (`N.subgroupOf L`), the extra centralizer condition is vacuous — a `y` centralizing
a nontrivial `x ∈ N` lands in the kernel `N` (`IsFrobeniusGroup.centralizer_kernel_le`), so the
support is just `N^#`.  This is the **non-circular** upstream twin of the §16
`centralizerSupport_sharpSubgroup_eq_of_frobenius`: it takes the Frobenius structure as a hypothesis
(supplied for the (12.16) witness by (12.10) `witness_L_frobenius`) rather than routing through the
final (12.7), so it is available before the minimal-counterexample machinery. -/
theorem centralizerSupport_sharp_eq_of_frobenius [Finite G] {M N : Subgroup G} {C : Subgroup ↥M}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (N.subgroupOf M) C) (hNM : N ≤ M) :
    OddOrder.GroupTheory.centralizerSupport (OddOrder.GroupTheory.sharpSubgroup N) M
      = OddOrder.GroupTheory.sharpSubgroup N := by
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyM, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxM : x ∈ M := hNM hxN
    have hxMsub : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyM⟩ : ↥M) ∈ N.subgroupOf M :=
      hfrob.centralizer_kernel_le _ hxMsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hNM hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

/-- **Ambient match for the (6.8) Sibley setup**: the `H^#`-image `sharpImage (H.subgroupOf L)` of
the Fitting kernel (`H = L_F`), pushed back to `G`, is exactly the type-I Dade support
`A(L) = typeIA L`.  Here `A(L) = centralizerSupport (H^#) L` (`typeIA` def) collapses to `H^#` for
the **Frobenius** `L` (`centralizerSupport_sharp_eq_of_frobenius`, non-circular from `hfrob`), and
`(H.subgroupOf L).map L.subtype = H ⊓ L = H` (`subgroupOf_map_subtype`, `H ≤ L`) matches the two
`H^#` descriptions.  This is the ambient identification that lets the (6.8) `SibleyDadeHypothesis`
(Dade datum on `sharpImage H`) reuse the (12.1) datum `hyp.dadeData.dade` (on `A(L)`), preserving
the isometry `hyp.tau` exactly. -/
theorem sharpImage_H_subgroupOf_eq_typeIA [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L) = typeIA L hyp.typeI := by
  have hmap : (hyp.H.subgroupOf L).map L.subtype = hyp.typeI.typeF.H := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hyp.typeI.typeF.H_le
  rw [show typeIA L hyp.typeI
        = OddOrder.GroupTheory.centralizerSupport
          (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H) L from rfl,
    centralizerSupport_sharp_eq_of_frobenius (N := hyp.typeI.typeF.H) hfrob hyp.typeI.typeF.H_le]
  simp only [OddOrder.Peterfalvi.S08.sharpImage, OddOrder.GroupTheory.sharpSubgroup, hmap]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Structural input for Peterfalvi (12.6) — TI-kernel Frobenius case (6.8)(c1).**

For the (6.8) case-(c1) route, `L` is Frobenius **and** `H^#` is a TI-subset of `G`
(Peterfalvi (6.8)(a) requires *both*: being Frobenius is (c1), but the ambient TI-ness is a
separate hypothesis).  Under TI, the §4 Dade datum's local subgroups vanish
(`dade.H a = ⊥`), which is exactly the `SibleyDadeHypothesis.dade_H_eq_bot` field, so a
`SibleyTarget` is available.

**Note (2026-07-01, issue 2032):** the earlier `_hfrob`-only signature was *unsound* — the (12.16)
witness `L` is Frobenius but its `H^#` is **not** TI in `G` (Peterfalvi (12.10): "By (12.9), `H^#`
is
not a TI-subset of `G`"), so `dade_H_eq_bot` fails there.  The `_hTI` hypothesis restores soundness;
the witness (non-TI) is handled by the case-(b)/(c) routes of `frobenius_typeI_coherent`, not by
this
TI-only carrier.

**Construction (2026-07-14, carve-out issue 9077)**: kernel `H = (L_F).subgroupOf L`; the Frobenius
witness supplies the split/nontriviality fields, `L_F = maxNilpotentNormalHall` the nilpotency.  The
TI bound `N_G(H)` collapses to `L` through the (8.15) normalizer identification
`hyp.dadeData.normalizer_eq` (`N_G(A(L)) = L`) and `A(L) = H^#` for Frobenius `L`
(`typeIA_eq_sharp_of_frobenius`, `normalizer_sharpSubgroup`).  The §4 Dade datum is the (12.1)
`hyp.dadeData.dade` recoordinated along `sharpImage H = A(L)`
(`sharpImage_H_subgroupOf_eq_typeIA`), so the Sibley map *is* `hyp.tau` exactly
(`dadeIntegralCharacterMap_transport_ambient`), and its local subgroups vanish by the (2.3) reverse
direction (`H_eq_bot_of_isTISubset`).  The `hodd` hypothesis feeds `card_L_odd` (Peterfalvi works
throughout with odd-order `G`; the earlier `hodd`-less signature was statement-level unprovable —
counter-model `G = S₄`, `L = S₃` — cf. the `hG.odd`-fed `card_L_odd` of
`typeVSibleyDadeHypothesis`; faithfulness fix approved by issue 9077 HUB RULING #4′). -/
noncomputable def sibleyTarget_frobI [Fintype G] {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)] (hyp : Hypothesis L)
    (hodd : Odd (Nat.card G))
    (_hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C)
    (_hTI : OddOrder.GroupTheory.IsTISubset
      (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H)
      (Subgroup.normalizer (hyp.typeI.typeF.H : Set G))) :
    CoherenceWiring.SibleyTarget hyp.tau hyp.Sset hyp.A := by
  -- Reconcile the four instance binders with the scoped `FiniteInduce` instances baked into
  -- `hyp.tau`/`hyp.Sset`/`hyp.A` (all four classes are subsingletons; `Finite G` proofs are
  -- definitionally irrelevant), so the whole construction lives in one instance world.
  rename_i iFG iFL iIL iIG
  haveI hFin : Finite G := hyp.finiteG
  obtain rfl : iFG = OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype :=
    Subsingleton.elim _ _
  obtain rfl : iFL = OddOrder.Peterfalvi.S12.FiniteInduce.finiteSubFintype L :=
    Subsingleton.elim _ _
  obtain rfl : iIL = OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC L :=
    Subsingleton.elim _ _
  obtain rfl : iIG = OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG :=
    Subsingleton.elim _ _
  -- The target lives in `Type`, so extract the Frobenius complement by choice.
  let C : Subgroup ↥L := _hfrob.choose
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C :=
    _hfrob.choose_spec
  -- Support-set identifications: `sharpImage ((L_F).subgroupOf L) = A(L) (= (L_F)^#)`.
  have hset : OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L)
      = typeIA L hyp.typeI := sharpImage_H_subgroupOf_eq_typeIA hyp hfrob
  have hEq : typeIA L hyp.typeI
      = OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L) := hset.symm
  -- `A(L) = (L_F)^#` for the Frobenius `L` (the non-circular upstream twin of
  -- `typeIA_eq_sharp_of_frobenius`, which is defined only later in this file).
  have hsharp : typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H :=
    centralizerSupport_sharp_eq_of_frobenius hfrob hyp.typeI.typeF.H_le
  -- The (6.8.a) TI in the `L`-relative form: the TI bound `N_G(H)` collapses to `L`
  -- through the (8.15) normalizer identification `N_G(A(L)) = L`.
  have hNeq : Subgroup.normalizer (hyp.typeI.typeF.H : Set G) = L := by
    rw [← OddOrder.Peterfalvi.S12.normalizer_sharpSubgroup, ← hsharp]
    exact hyp.dadeData.normalizer_eq
  have hTI_L : OddOrder.GroupTheory.IsTISubset
      (OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L)) L := by
    rw [hset, hsharp]
    exact _hTI.mono hNeq.le
  -- The (12.1) Dade datum recoordinated to the Sibley support: the *identical* datum
  -- transported along `hEq`, so the Dade isometry is preserved exactly.
  have hconj' : (hEq ▸ hyp.dadeData.dade :
      OddOrder.Peterfalvi.S04.Hypothesis G
        (OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L)) L).HConjInvariant :=
    OddOrder.Peterfalvi.S04.Hypothesis.hConjInvariant _
  have hoddL : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  refine
    { H := hyp.H.subgroupOf L
      invH := inferInstance
      sib :=
        { W1 := C
          H_ne_bot := hfrob.ne_bot_kernel
          H_normal := hfrob.isNormal
          H_nilpotent := ?_
          split := hfrob.isComplement
          W1_nontrivial := hfrob.ne_bot_complement
          card_L_odd := hoddL
          H_sharp_ti := hTI_L
          dade := hEq ▸ hyp.dadeData.dade
          dade_H_eq_bot := fun a =>
            OddOrder.Peterfalvi.S04.Hypothesis.H_eq_bot_of_isTISubset _ hTI_L a
          S := hyp.Sset
          S_eq := rfl
          cases := Or.inl hfrob }
      tau_eq :=
        dadeIntegralCharacterMap_transport_ambient hEq hyp.dadeData.dade
      S_eq := rfl
      A0_eq := by rw [hset]; rfl }
  -- `H = L_F` is nilpotent: `maxNilpotentNormalHall` nilpotency transported to the
  -- `↥L`-coordinate along `subgroupOfEquivOfLe`.
  have : Group.IsNilpotent ↥(hyp.typeI.typeF.H) := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.H_le).symm

end OddOrder.Peterfalvi.S14

-- ===== OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructure.lean =====
namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6)**: if `L` is Frobenius with kernel `H = L_F`, then `S` is coherent.

The textbook proof **case-splits** on the type-I trichotomy `Definition (8.3)` (carried by
`hyp.typeI.alternative`): (a) `H^#` TI in `G` → (6.8) (`sibleyTarget_frobI`); (b) `H` abelian rank 2
→ equal-degree (5.7) (`frobenius_typeI_coherent_of_abelianKernel`); (c) `|L/H| ∣ p−1` → (6.5.c)
(`frobenius_typeI_coherent_of_cyclicQuotient`).  The (12.16) witness lands in case (b) or (c)
(Peterfalvi (12.10): its `H^#` is *not* TI), so the (6.8) route alone is insufficient — the earlier
single-`sibleyTarget_frobI` proof was unsound (issue 2032).  This assembly carries no `sorry` of its
own.  Cases (b) `frobenius_typeI_coherent_of_abelianKernel` and (c)
`frobenius_typeI_coherent_of_cyclicQuotient` are `sorry`-free, as is case (a) via the (6.8) target
`sibleyTarget_frobI` (its (8.18.c) obligation `nonconjugate_diffImage_inner_zero` was closed by the
(12.3) bar-trick descent, 2026-07-03). -/
theorem frobenius_typeI_coherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hyp : Hypothesis L)
    (hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  rcases hyp.typeI.alternative with hTI | hab | hexp
  · exact CoherenceWiring.coherent_of_sibleyTarget (sibleyTarget_frobI hyp hG.odd hfrob hTI)
  · exact frobenius_typeI_coherent_of_abelianKernel hG hyp hfrob hab
  · exact frobenius_typeI_coherent_of_cyclicQuotient hG hyp hfrob hexp

end OddOrder.Peterfalvi.S14

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

-- ===== OddOrder/Peterfalvi/S14_MaximalI/NormPackage.lean =====
namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **The type-I Dade support is `H#`** (Peterfalvi (8.3)/(12.1) for the witness subgroup `L`).
`typeIA L = centralizerSupport (H#) L` collapses to `H# = (H : Set G) \ {1}` (`H = L_F`): the
Frobenius structure of `L` (from (12.7) `typeI_frobenius`) makes the centralizer condition vacuous
on `H#` (`IsFrobeniusGroup.centralizer_kernel_le`).  This supplies the `A = H#` shape that
`S09.Cert.hypothesis78OfDade` needs (the `hAH` argument of the §12→§7 Dade bridge).

Re-derives the `centralizerSupport = sharp` argument of
`S16.centralizerSupport_sharpSubgroup_eq_of_frobenius` — which lives downstream of `S14` and so
cannot be cited here; a hub dedup hoisting that pure-group-theory fact to a shared file (e.g.
`MaximalSubgroupType`) is tracked in issue 1013. -/
theorem Hypothesis.typeIA_eq_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.GroupTheory.typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H := by
  obtain ⟨fdata, _⟩ := typeI_frobenius hG hnoV hyp.maximal ⟨hyp.typeI⟩
  have hKf : fdata.typeI.typeF.H = hyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, hyp.typeI.typeF.H_eq]
  exact hyp.typeIA_eq_sharp_of_frobenius (hKf ▸ fdata.frobenius)

end OddOrder.Peterfalvi.S14

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

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

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

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_ComplementStructure.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `W₁` (order `q`) is coprime to the type-I Frobenius kernel `L_F` (`q ∤ |L_F|`).  This is
Peterfalvi's "`W₁ ∩ H = 1`", from (8.17.a).

*Proof.*  `L` is type I while `S` and `T` are type non-I maximal subgroups, so `L` is conjugate to
neither (`not_conj_of_isTypeI_of_isTypeNonI`).  Hence (8.17.a) `card_LF_coprime_pq` gives
`|L_F| ⟂ p q`, in particular `|L_F| ⟂ q`, i.e. `q ∤ |L_F|`; the kernel `H = frob.typeI.typeF.H`
equals `L_F = maxNilpotentNormalHall L` (`TypeFData.H_eq`, so the "kernel_eq_MF" identification is
*not* opaque) and `|H.subgroupOf L| = |H|`.  The only gated input is `card_LF_coprime_pq` (B2,
BG Theorem E, owner F). -/
theorem q_not_dvd_kernel [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L) :
    ¬ hyp.q ∣ Nat.card ↥(frob.typeI.typeF.H.subgroupOf L) := by
  -- `L` is type I, while `S`, `T` are type non-I maximal: `L` is conjugate to neither.
  have hnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.S_maximal hyp.S_nonI
  have hnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.T_maximal hyp.T_nonI
  -- (8.17.a): `|L_F| ⟂ p q`, hence `q ∤ |L_F|`.
  have hcop := card_LF_coprime_pq _hG hyp hLmax hLI hnconjS hnconjT
  have hcopq : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.q :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left hyp.q hyp.p) hcop
  have hnotdvd : ¬ hyp.q ∣ Nat.card ↥(maxNilpotentNormalHall L) :=
    hyp.q_prime.coprime_iff_not_dvd.mp hcopq.symm
  -- `H = L_F = maxNilpotentNormalHall L`, and `|H.subgroupOf L| = |H|`.
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hHleL : frob.typeI.typeF.H ≤ L := by
    rw [hHeq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleL).toEquiv, hHeq]
  exact hnotdvd

/-- (13.17.a/b)-strengthening of (12.7): the type-I Frobenius decomposition of `L` can be taken
with the complement containing `W₁` — Peterfalvi's "let `E` be a complement to `H` in `L` such
that `W₁ ⊂ E`".  Since `W₁ ≤ N_G(U) ≤ L` is coprime to the kernel (`q ∤ |L_F|`,
`q_not_dvd_kernel`), Schur–Zassenhaus complement conjugacy
(`exists_conj_le_of_isComplement'_of_coprime`) places `W₁` in a conjugate `E₀^x` of any complement
`E₀`, which is again a Frobenius complement (`IsFrobeniusGroup.conjComplement`).  The coprimality
goes through the `kernel_eq_MF` carrier. -/
theorem exists_typeIFrobeniusData_W1_le [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLtypeI : IsTypeI L) (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    ∃ frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L, frob.kernel_eq_MF ∧
      hyp.W1 ≤ frob.complement.map L.subtype := by
  obtain ⟨frob₀, hker₀⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hnoV hLmax hLtypeI
  have hW1L : hyp.W1 ≤ L := hyp.W1_normalizes_U.trans hNUL
  have : (frob₀.typeI.typeF.H.subgroupOf L).Normal := frob₀.frobenius.isNormal
  -- `L` (maximal) is solvable, hence so is the kernel.
  have hLsolv : Group.IsSolvable ↥L :=
    _hG.isSolvable_of_lt_top L (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hLmax).1)
  have : Group.IsSolvable ↥(frob₀.typeI.typeF.H.subgroupOf L) := inferInstance
  -- coprimality `|W₁| = q` to `|L_F|`.
  have hcop : Nat.Coprime (Nat.card ↥(hyp.W1.subgroupOf L))
      (Nat.card ↥(frob₀.typeI.typeF.H.subgroupOf L)) := by
    have hW1card : Nat.card ↥(hyp.W1.subgroupOf L) = hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1L).toEquiv]
      exact hyp.q_eq_card_W1.symm
    rw [hW1card]
    exact (hyp.q_prime.coprime_iff_not_dvd).mpr (q_not_dvd_kernel _hG hyp hLmax hLtypeI frob₀)
  -- `W₁` lies in a conjugate `E₀^x` of the complement.
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    inferInstance frob₀.frobenius.isComplement hcop
  refine ⟨{ frob₀ with
      complement := frob₀.complement.map (MulAut.conj x).toMonoidHom
      frobenius := frob₀.frobenius.conjComplement x }, frob₀.kernel_eq_MF_holds, ?_⟩
  -- `W₁ = (W₁.subgroupOf L).map L.subtype ≤ (E₀^x).map L.subtype`.
  have : hyp.W1 = (hyp.W1.subgroupOf L).map L.subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le hW1L]
  rw [this]
  exact Subgroup.map_mono hx

/-- **Frobenius index bridge** (Pf (14.11), structural): for a type-I maximal `M` with
`TypeIFrobeniusData`, the index `|M : M_F|` of the Fitting kernel equals the order of the Frobenius
complement.  Immediate from the complement structure `M = M_F ⋊ complement` (`IsComplement'`) and
the
kernel identity `typeF.H = M_F`.  Supplies the `e = |M : K| = p q` half of `MHypothesis`
(`e_eq_index` + `complement_card_eq_pq`): combined with the V-side `complement_card_eq_pq`
(`= p q`),
the Fitting-kernel index of the type-I maximal over `N_G(V)` is `p q`. -/
theorem typeIFrobenius_kernel_index_eq_complement {M : Subgroup G}
    (data : OddOrder.Peterfalvi.S14.TypeIFrobeniusData M) :
    ((maxNilpotentNormalHall M).subgroupOf M).index = Nat.card data.complement := by
  rw [← data.typeI.typeF.H_eq]
  exact data.frobenius.isComplement.symm.index_eq_card

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

/-- **Existence of the bundle for any type-I maximal subgroup** (Peterfalvi (12.1) +
(12.6) + (12.7)): the Dade setup from `exists_typeI_hypothesis`, the Frobenius witness
from the headline (12.7) `typeI_frobenius`, the coherence from
`frobenius_typeI_coherent`, and the placed family from
`exists_witness_placed_family`. -/
theorem nonempty (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G) (hLtypeI : IsTypeI L) :
    Nonempty (TypeICoherent78Data L) := by
  classical
  obtain ⟨typeIHyp⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis hG hLmax hLtypeI
  obtain ⟨fdata, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV hLmax hLtypeI
  -- Transport the Frobenius witness to `typeIHyp`'s kernel (both are `L_F`).
  have hHeq : fdata.typeI.typeF.H = typeIHyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, typeIHyp.typeI.typeF.H_eq]
  have hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((typeIHyp.typeI.typeF.H).subgroupOf L) fdata.complement := by
    rw [← hHeq]; exact fdata.frobenius
  obtain ⟨coh⟩ := OddOrder.Peterfalvi.S14.frobenius_typeI_coherent hG typeIHyp
    ⟨fdata.complement, hFrob⟩
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ :=
    OddOrder.Peterfalvi.S14.exists_witness_placed_family typeIHyp
  exact ⟨{ typeIHyp := typeIHyp
           C := fdata.complement
           hFrob := hFrob
           coh := coh
           n := n
           θ := θ
           ind1H := ind1H
           ind1H_ne_zero := hind1H
           deg0 := hdeg0
           triv := htriv
           inj := hinj
           cover := hcover
           typeIA_eq :=
             OddOrder.Peterfalvi.S14.Hypothesis.typeIA_eq_sharp hG hnoV typeIHyp }⟩

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

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.5), core exclusion**: under the §14 normalization `q < p` and the type-II
fact `N_G(U) ⊄ S`, the `W₁`-containing Frobenius complement `E` of the type-I maximal
`L ⊇ N_G(U)` is not contained in `Q`.

*Proof (Pf p.87).*  If `E ≤ Q` then `E = E ⊓ Q = W₁` (`complement_inf_Q_eq_W1`), so the
Fitting-kernel index of `L` is `e = |W₁| = q < p`.  The (13.19.c) dichotomy
(`typeIOrthogonalityGridData_of_coherent78`) then cannot hold in case (c2) (which forces
`p ≤ e`), so the (c1) bound `(|H|−1)/e ≤ (u−1)/q` holds with `e = q`, giving `|H| ≤ u`.  With
`U ≤ H` ((13.17.b), hypothesis `hUH`) and `u ≤ |U|` this forces `H = U`, so
`L = H ⋊ E = U W₁ ≤ S` — contradicting `N_G(U) ≤ L` and `N_G(U) ⊄ S`. -/
theorem complement_not_le_Q_of_c_eq_one_and_d_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) (hd1 : hyp.d = 1)
    (hTTypeII : IsTypeII hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype)
    (pins : NuGridSupplyData hyp) :
    ¬ frob.complement.map L.subtype ≤ hyp.Q := by
  intro hle
  -- `E ≤ Q` collapses `E` to `E ⊓ Q = W₁` (the proven (13.17.c) half)
  have hEW1 : frob.complement.map L.subtype = hyp.W1 := by
    have h := complement_inf_Q_eq_W1 _hG hyp hTTypeII frob hW1E
    rwa [inf_eq_left.mpr hle] at h
  -- hence the Fitting-kernel index of `L` is `|E| = |W₁| = q`
  have hEcard : Nat.card ↥frob.complement = hyp.q := by
    rw [show Nat.card ↥frob.complement
          = Nat.card ↥(frob.complement.map L.subtype) from
        Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
          L.subtype_injective).toEquiv, hEW1]
    exact hyp.q_eq_card_W1.symm
  have hindex : ((maxNilpotentNormalHall L).subgroupOf L).index = hyp.q := by
    rw [typeIFrobenius_kernel_index_eq_complement frob, hEcard]
  -- the (13.19) grid data for `L`
  obtain ⟨dataL⟩ := OddOrder.Peterfalvi.S16.TypeICoherent78Data.nonempty _hG hnoV hLmax hLI
  have hHL : dataL.typeIHyp.H = maxNilpotentNormalHall L := dataL.typeIHyp.typeI.typeF.H_eq
  set g := typeIOrthogonalityGridData_of_coherent78_of_c_eq_one_and_d_eq_one
    _hG hnoV hyp hc1 hd1 dataL (pins := pins) with hgdef
  have he_q : g.e = hyp.q := by rw [← g.e_eq_index, hindex]
  -- case (c2) is impossible: `p ≤ e = q < p`
  rcases g.caseC with ⟨-, hbound⟩ | ⟨-, hpe⟩
  swap
  · rw [he_q] at hpe
    omega
  -- case (c1): `(|H|−1)/q ≤ (u−1)/q` forces `|H| ≤ u ≤ |U| ≤ |H|`, so `H = U`
  rw [he_q] at hbound
  have hq0 : (0 : ℚ) < (hyp.q : ℚ) := by exact_mod_cast hyp.q_prime.pos
  have hle_nat : Nat.card ↥dataL.typeIHyp.H - 1 ≤ hyp.u - 1 := by
    have h : ((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) ≤ ((hyp.u - 1 : ℕ) : ℚ) := by
      have hmul := mul_le_mul_of_nonneg_right hbound hq0.le
      rwa [div_mul_cancel₀ _ hq0.ne', div_mul_cancel₀ _ hq0.ne'] at hmul
    exact_mod_cast h
  have hupos : 0 < hyp.u := by
    rcases Nat.eq_zero_or_pos hyp.u with h0 | h
    · exfalso
      have hcard := hyp.card_U_eq_uc
      rw [h0, Nat.zero_mul] at hcard
      exact absurd hcard Nat.card_pos.ne'
    · exact h
  have hu_le_U : hyp.u ≤ Nat.card ↥hyp.U := by
    rw [hyp.card_U_eq_uc]
    have hc : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
    exact Nat.le_mul_of_pos_right _ hc
  have hU_le_H : Nat.card ↥hyp.U ≤ Nat.card ↥(maxNilpotentNormalHall L) :=
    Subgroup.card_le_of_le hUH
  have hHpos : 0 < Nat.card ↥dataL.typeIHyp.H := Nat.card_pos
  have hcard_eq : Nat.card ↥(maxNilpotentNormalHall L) = Nat.card ↥hyp.U := by
    rw [← hHL] at hU_le_H ⊢
    omega
  have hUeq : maxNilpotentNormalHall L = hyp.U :=
    (Subgroup.eq_of_le_of_card_ge hUH (le_of_eq hcard_eq)).symm
  -- `L = H ⊔ E = U ⊔ W₁ ≤ S`, contradicting `N_G(U) ≤ L` with `N_G(U) ⊄ S`
  have hsup : (maxNilpotentNormalHall L).subgroupOf L ⊔ frob.complement = ⊤ := by
    have h := frob.frobenius.isComplement.sup_eq_top
    rwa [frob.typeI.typeF.H_eq] at h
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by
      rw [hyp.S_deriv_eq_PU]; exact le_sup_right
    exact h1.trans (Subgroup.map_subtype_le _)
  have hW1S : hyp.W1 ≤ hyp.S := by
    have h1 : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    rw [hyp.W_eq_inter] at h1
    exact h1.trans inf_le_left
  have hLS : L ≤ hyp.S := by
    have hLtop : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hLtop, ← hsup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.subgroupOf_map_subtype]
      refine inf_le_left.trans ?_
      rw [hUeq]
      exact hUS
    · rw [hEW1]
      exact hW1S
  exact hNUS (hNUL.trans hLS)

/-- **Peterfalvi (14.5) order consequence.**  Under the (14.5) hypotheses the `W₁`-containing
Frobenius complement `E` of `L` has order `p q`.

*Proof (Pf p.82/p.87).*  `E ⊆ Q W₂` (`complement_le_QW2_of_D_eq_bot`), and `Q ⋊ W₂` has
`Q ◁ Q W₂` with
`[Q W₂ : Q] = |W₂| = p` (`Q_W2_structure`).  The relative index `[E : E ∩ Q]` divides
`[Q W₂ : Q] = p` (normal-subgroup relative index inside `↥(Q W₂)`) and is `≠ 1` by the (14.5)
exclusion `E ⊄ Q` (`complement_not_le_Q`), hence `= p`; with `E ∩ Q = W₁` of order `q`
(`complement_inf_Q_eq_W1`), `|E| = |E ∩ Q| · [E : E ∩ Q] = q p`. -/
theorem complement_card_eq_pq_of_c_eq_one_and_d_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) (hd1 : hyp.d = 1)
    (hTTypeII : IsTypeII hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype)
    (pins : NuGridSupplyData hyp) :
    Nat.card ↥frob.complement = hyp.p * hyp.q := by
  set Em := frob.complement.map L.subtype with hEm
  set Hg := hyp.Q ⊔ hyp.W2 with hHg
  -- `E ∩ Q = W₁` (proven (13.17.c) half); the (14.5) exclusion `E ⊄ Q`.
  have hInf := complement_inf_Q_eq_W1 _hG hyp hTTypeII frob hW1E
  have hnle := complement_not_le_Q_of_c_eq_one_and_d_eq_one
    _hG hnoV hyp hc1 hd1 hTTypeII hqp hNUS hLmax hLI hNUL hUH frob hW1E pins
  -- `E ⊆ Q W₂` (Huppert step) and the `Q ⋊ W₂` structure.
  have hDbot : hyp.D = ⊥ :=
    Subgroup.card_eq_one.mp (by rw [← hyp.d_eq_card_D]; exact hd1)
  have hEH : Em ≤ Hg :=
    complement_le_QW2_of_D_eq_bot _hG hyp hTTypeII hDbot frob hW1E
  obtain ⟨hWnorm, hdisj, _⟩ := Q_W2_structure _hG hyp hTTypeII
  have hQleH : hyp.Q ≤ Hg := le_sup_left
  -- `|E ∩ Q| = |W₁| = q`.
  have hInfCard : Nat.card ↥(Em ⊓ hyp.Q) = hyp.q := by rw [hInf]; exact hyp.q_eq_card_W1.symm
  -- `Q ◁ Q W₂` (as `Q W₂ ≤ N_G(Q)`).
  have hQnorm : (hyp.Q.subgroupOf Hg).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleH).mpr (sup_le Subgroup.le_normalizer hWnorm)
  -- `|Q W₂| = |Q| · p`.
  have hHcard : Nat.card ↥Hg = Nat.card ↥hyp.Q * hyp.p := by
    have h := OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hWnorm
      (show hyp.W2 ⊓ hyp.Q = ⊥ by rw [inf_comm]; exact hdisj)
    rw [hHg, sup_comm, h, ← hyp.p_eq_card_W2]
    exact mul_comm _ _
  have hQpos : 0 < Nat.card ↥hyp.Q := Nat.card_pos
  -- `[Q W₂ : Q] = p`.
  have hindexH : (hyp.Q.subgroupOf Hg).index = hyp.p := by
    have hmul := Subgroup.card_mul_index (hyp.Q.subgroupOf Hg)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleH).toEquiv, hHcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left hQpos hmul
  -- `[E : E ∩ Q] = Q.relIndex E` divides `[Q W₂ : Q] = p`, and is `≠ 1` (`E ⊄ Q`), hence `= p`.
  have hdvd : hyp.Q.relIndex Em ∣ hyp.p := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (H := hyp.Q.subgroupOf Hg)
      (K := Em.subgroupOf Hg)
    rwa [Subgroup.relIndex_subgroupOf hEH, hindexH] at h1
  have hne1 : hyp.Q.relIndex Em ≠ 1 := fun h => hnle (Subgroup.relIndex_eq_one.mp h)
  have hrel : hyp.Q.relIndex Em = hyp.p :=
    (hyp.p_prime.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  -- `|E| = |E ∩ Q| · [E : E ∩ Q] = q · p`.
  have hEmcard : Nat.card ↥Em = hyp.q * hyp.p := by
    have hmul := Subgroup.card_mul_index (hyp.Q.subgroupOf Em)
    rw [show (hyp.Q.subgroupOf Em).index = hyp.p from hrel, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Em ⊓ hyp.Q ≤ Em)).toEquiv,
      hInfCard] at hmul
    exact hmul.symm
  -- transfer `|E.map| = |E|`.
  rw [show Nat.card ↥frob.complement = Nat.card ↥Em from
    Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv, hEmcard]
  exact mul_comm _ _

/-- **Peterfalvi (14.5), full form**: the `W₁`-containing Frobenius complement of the type-I
subgroup `L` over `N_G(U)` has order `p q` and contains a conjugate `W₂^y` (`y ∈ Q`).

Assembled from the order argument (`complement_card_eq_pq`) and the group-theoretic `∃ y`
extraction (`exists_mem_conj_W2_le_of_dvd_card`, Schur–Zassenhaus), the latter fed `E ⊆ Q W₂`
by the Huppert step (`complement_le_QW2_of_D_eq_bot`).  The `W₁ ⊆ E` hypothesis records
Peterfalvi's choice
"let `E` be a complement to `H` in `L` such that `W₁ ⊂ E`". -/
theorem typeI_overNormalizer_complement_of_c_eq_one_and_d_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) (hd1 : hyp.d = 1)
    (hTTypeII : IsTypeII hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype)
    (pins : NuGridSupplyData hyp) :
    Nat.card ↥frob.complement = hyp.p * hyp.q ∧
      ∃ y ∈ hyp.Q, (MulAut.conj y • hyp.W2 : Subgroup G) ≤
        frob.complement.map L.subtype := by
  have hcard := complement_card_eq_pq_of_c_eq_one_and_d_eq_one
    _hG hnoV hyp hc1 hd1 hTTypeII hqp hNUS hLmax hLI hNUL hUH frob hW1E pins
  refine ⟨hcard, ?_⟩
  obtain ⟨hWnorm, hdisj, hpQ⟩ := Q_W2_structure _hG hyp hTTypeII
  have hDbot : hyp.D = ⊥ :=
    Subgroup.card_eq_one.mp (by rw [← hyp.d_eq_card_D]; exact hd1)
  have hEQW2 := complement_le_QW2_of_D_eq_bot _hG hyp hTTypeII hDbot frob hW1E
  -- `Q` is solvable: `Q = T_F ≤ T < ⊤`.
  have hQsolv : Group.IsSolvable ↥hyp.Q := by
    have hQT : hyp.Q ≤ hyp.T := by
      rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
    have hTlt : hyp.T < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1
    exact _hG.isSolvable_of_lt_top hyp.Q (lt_of_le_of_lt hQT hTlt)
  -- `p ∣ |E.map| = |E| = p q`.
  have hpE : hyp.p ∣ Nat.card ↥(frob.complement.map L.subtype) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv.symm, hcard]
    exact dvd_mul_right hyp.p hyp.q
  exact exists_mem_conj_W2_le_of_dvd_card hWnorm hQsolv hdisj hyp.p_prime
    hyp.p_eq_card_W2.symm hpQ hEQW2 hpE

/-- **Peterfalvi (14.5), packaged**: if `S` is type II (with the §14 normalization `q < p` and
the type-II consequence `N_G(U) ⊄ S`), a maximal subgroup over `N_G(U)` is type-I Frobenius,
contains `U` in its kernel, and its `W₁`-containing complement has order `p q` with a conjugate
`W₂^y` inside.  Assembled from the type-I existence (13.17.a/b,
`exists_typeI_maximal_overNormalizer_U`), a `W₁`-containing Frobenius decomposition
(`exists_typeIFrobeniusData_W1_le`), and the (14.5) complement structure
(`typeI_overNormalizer_complement`). -/
theorem typeII_overNormalizer_frobenius_of_c_eq_one_and_d_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) (hd1 : hyp.d = 1)
    (hSTypeII : IsTypeII hyp.S) (hTTypeII : IsTypeII hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S)
    (pins : NuGridSupplyData hyp) :
    ∃ data : TypeIOverNormalizerData hyp,
      data.frobenius.kernel_eq_MF ∧ (hyp.U ≤ data.H) := by
  obtain ⟨L, hLmax, hLtypeI, hNUL, hUH⟩ :=
    exists_typeI_maximal_overNormalizer_U _hG hnoV hyp hSTypeII hTTypeII
  obtain ⟨frob, hker, hW1E⟩ := exists_typeIFrobeniusData_W1_le _hG hnoV hyp hLmax hLtypeI hNUL
  obtain ⟨hcard, hy⟩ := typeI_overNormalizer_complement_of_c_eq_one_and_d_eq_one
    _hG hnoV hyp hc1 hd1 hTTypeII hqp hNUS
      hLmax hLtypeI hNUL hUH frob hW1E pins
  exact ⟨⟨L, maxNilpotentNormalHall L, hLmax, rfl, hNUL, frob, hUH, hcard, hy⟩, hker, hUH⟩

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

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (11.9)/(14.9), the Type-IV exclusion** — the deep content of the type
determination, now discharged.  Coq `FTtype34_structure` (Peterfalvi (11.9), `PFsection11.v:1001`,
consumed at `PFsection14.v:735`) pins a non-type-II type-`P` maximal `T` to Type III (not IV) via
the character/Galois argument `suffices galM : typeP_Galois MtypeP` (`PFsection11.v:1139`) — the
`η`-grid projection computation `a₁₁ = a₁₀ = 0`.

Formalised as the universal (11.9.c) Type-IV exclusion `not_isTypeIV_of_mem_maximalSubgroups`
(`S13_NonGaloisExclusion`, sorry-free): the `IsMulCommutative V` residual that used to live here
follows from `cyclic V ⟸ typeP_Galois T`, whose full §5–§13 chain
(`not_isTypeIV_of_hypothesis`/`U_isCyclic_of_hypothesis`) is landed.  The direct cite became
possible once the §12–16 import inversion (issue 9093) removed `S13_NonGaloisExclusion`'s
transitive dependency on §16. -/
theorem T_not_isTypeIV_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    ¬ OddOrder.GroupTheory.IsTypeIV hyp.base.T :=
  OddOrder.Peterfalvi.S13.not_isTypeIV_of_mem_maximalSubgroups hG hyp.base.T_maximal

/-- **Peterfalvi (14.9), the type determination** — Coq `PFsection14`
`have [_ _ [Ttype3 _]] := FTtype34_structure maxT TtypeP notTtype2` (line 735): a type-`P` maximal
subgroup that is *not* type II is type III.  In σ-theoretic terms, `IsTypeP1 T` (equivalently
`¬ IsTypeP2 T` given `IsTypeP T`) forces `T` to be structurally Type III.

**Fully reduced to the single (11.9) residual `T_not_isTypeIV_of_isTypeP1`.**  The type dictionary
`proposition_type_classification` (BG Prop 16.1, proven) gives, from `IsTypeP1 T`, either Type
III/IV
(if `M_F ≠ M_σ`) or Type V (if `M_F = M_σ`).  **Type V is excluded outright** by the (10.10)
hypothesis `hnoV` (instantiate with the axiom-clean `no_typeV_maximal_unconditional`,
`S12_Noncoherence`; issue 9087), so `M_F ≠ M_σ` and `T` is Type III or IV. Excluding Type IV — the
genuine (11.9) Galois/character
content — is the isolated residual `T_not_isTypeIV_of_isTypeP1`.  The Type-V exclusion and the
III/IV
structural wiring (incl. the `TypeIIIData.normalizer_le` field, bundled into the clause-(c)
disjunction) are proven here. -/
theorem T_isTypeIII_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (hyp : Hypothesis (G := G)) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    OddOrder.GroupTheory.IsTypeIII hyp.base.T := by
  -- Type dictionary (BG Prop 16.1): `IsTypeP1 T` ⟹ III/IV (`M_F ≠ M_σ`) or V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.base.T_maximal
  -- Type V excluded universally by the (10.10) hypothesis `hnoV`, so `M_F ≠ M_σ`.
  have hMF : OddOrder.BG.Ch4.S15.MF hyp.base.T ≠ OddOrder.BG.Ch3.S10.Msigma hyp.base.T := fun h =>
    hnoV ⟨hyp.base.T, hyp.base.T_maximal, hdV.mpr ⟨hP1, h⟩⟩
  -- `T` is Type III or IV; exclude IV by the (11.9) residual.
  exact (hcIII_IV.mpr ⟨hP1, hMF⟩).resolve_right (T_not_isTypeIV_of_isTypeP1 hG hyp hP1)

/-- **Peterfalvi (14.9), reduced to its canonical residual.**  Starting from the symmetric
(13.1) non-type-I carrier, `T` is sharpened to BG type `P₂` (`κ(T) ≠ σ'(T)`; Coq `PFsection14`
`FTtypeP_min_typeII : FTtype T == 2`).  The `IsTypeP T` conjunct is discharged honestly from
`T_nonI` (`isTypeP_of_isTypeNonI`).

The residual `κ(T) ≠ σ'(T)` is proved by the (14.9) contradiction, following Coq
`FTtypeP_min_typeII` (`apply: contraLR v1p_gt_u1q => notTtype2`): were `κ(T) = σ'(T)` (i.e.
`IsTypeP1 T`), then `T` is Type III (`T_isTypeIII_of_isTypeP1`, the `FTtype34_structure`
determination), whence the character body forces `(v − 1)/p ≤ (u − 1)/q` (`T_typeIII_ratio_le`) —
contradicting (14.8) `key_inequality`'s `(v − 1)/p > (u − 1)/q`.

The two deep pieces are isolated as `T_typeIII_ratio_le` (character body) and
`T_isTypeIII_of_isTypeP1` (type determination), both consumed below.  The `>` half is (14.8): its
pure cyclotomic comparison lives upstream in `KeyInequalityArithmetic`, while the two
group-theoretic
order inputs are the direct (13.4) producer `T_side_caseB_facts` and the (13.15) producer
`Hypothesis.u_le_cyclotomicQuotient`.  Thus no forward reference through the later
`key_inequality` theorem is needed. -/
theorem T_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch4.S14.IsTypeP2 hyp.base.T := by
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.base.T_maximal hyp.base.T_nonI
  refine ⟨hP, ?_⟩
  -- (14.9), by contradiction (Coq `contraLR v1p_gt_u1q => notTtype2`): assume `κ(T) = σ'(T)`.
  intro hκeq
  -- Then `T` is type `P₁`, hence (Coq `FTtype34_structure`) structurally Type III.
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := ⟨hP, hκeq⟩
  have hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T := T_isTypeIII_of_isTypeP1 hG hnoV hyp hP1
  -- The character body then gives the type-III Γ-bridge estimate `(v − 1)/p ≤ (u − 1)/q`.
  have hle : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) :=
    T_typeIII_ratio_le hG hnoV hncH0C hyp hIII
  -- The arithmetic half of (14.8), separated from the later `key_inequality` packaging.
  have hratio := cyclotomic_ratio_gt_of_q_lt_p
    hyp.base.p_prime hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p
  -- Its T-side order input is the direct (13.4) producer, which is upstream of `T_isTypeP2`.
  have hvfull := (T_side_caseB_facts hG hyp).2
  -- The required S-side upper bound is the unconditional cyclotomic quotient estimate.
  have hu_le_full :
      hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    hyp.base.u_le_cyclotomicQuotient hG
  have hqpos : (0 : ℚ) < hyp.base.q := by
    exact_mod_cast hyp.base.q_prime.pos
  have hu_sub : ((hyp.base.u - 1 : ℕ) : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le_sub_right hu_le_full 1
  have hu_div : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) /
        (hyp.base.q : ℚ) :=
    div_le_div_of_nonneg_right hu_sub (le_of_lt hqpos)
  have hgt : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
    rw [hvfull]
    exact lt_of_le_of_lt hu_div hratio
  exact absurd hle (not_le.mpr hgt)

/-- **Peterfalvi (14.9)**: the subgroup `T` is of Type II.  `T` is of type `P₂`
(`T_isTypeP2`), and *every* type-`P₂` maximal subgroup is type II by the proven BG bridge
`isTypeII_of_isTypeP2`.  That bridge discharges
the deep `M'`-type-`F` structure — `IsTypeF (derivedInG T)` and `(T')_F = T_F` — internally
(`isTypeF_derivedInG_of_isTypeP2`), so the sole residual of (14.9) is the type-`P₂` fact
`T_isTypeP2`.
(Placed ahead of `exists_LHypothesis` so the §14 `T`-side chain — `typeII_overNormalizer_frobenius`
etc. — can cite `IsTypeII T` locally.) -/
theorem T_typeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    IsTypeII hyp.base.T :=
  OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.base.T_maximal (T_isTypeP2 hG hnoV hncH0C hyp)

end OddOrder.Peterfalvi.S16

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

/-- **Peterfalvi (14.3)**: a type-I maximal subgroup `L` over `N_G(U)` exists.  Constructed by
citing `S15.typeII_overNormalizer_frobenius_of_c_eq_one_and_d_eq_one` for the
type-I-over-normalizer Frobenius data (`S` is type II by `basic_structure` + (14.1) `q < p`);
the complement order `|E| = p q` is a field `complement_card_eq_pq` of that data ((14.5) —
the small (13.17.c) alternative `E = W₁` is excluded there via the (13.19.c) dichotomy under
`q < p` and `N_G(U) ⊄ S`, the latter supplied here through the L~S rule-out chain
`P_inf_U_eq_bot` → `coprime_card_U_card_P_of_disjoint` → `exists_conj_typeP_U_of_coprime` →
`not_normalizer_U_le_S`).  The (14.3.b) Dade data is not carried — it is unused by the §14
non-existence argument, so the carrier holds exactly the structural data the proof consumes.
Placed here (ahead of the (14.4)--(14.16) lemmas) so the mid-file numeric lemmas can construct
an `LHypothesis` to feed the S-side case-(9.7.b) data `caseB_for_S`. -/
theorem _root_.solution [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    Nonempty (LHypothesis hyp) := by
  obtain ⟨bdata, _⟩ := OddOrder.Peterfalvi.S15.basic_structure _hG hyp.base
  have hSII : IsTypeII hyp.base.S := bdata.q_lt_p_forces_typeII hyp.q_lt_p
  have hTII : IsTypeII hyp.base.T := T_typeII _hG hnoV hncH0C hyp
  obtain ⟨tdata⟩ := hSII
  have hNUS : ¬ Subgroup.normalizer (hyp.base.U : Set G) ≤ hyp.base.S :=
    OddOrder.Peterfalvi.S15.not_normalizer_U_le_S _hG hyp.base tdata
      (OddOrder.Peterfalvi.S15.exists_conj_typeP_U_of_coprime _hG hyp.base tdata
        (OddOrder.Peterfalvi.S15.coprime_card_U_card_P_of_disjoint hyp.base tdata
          (P_inf_U_eq_bot _hG hyp)))
  have hc1 : hyp.base.c = 1 :=
    hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply
  have hDbot : hyp.base.D = ⊥ := (T_side_caseB_facts _hG hyp).1
  have hd1 : hyp.base.d = 1 := by
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  obtain ⟨typeI_data, _, _⟩ :=
    OddOrder.Peterfalvi.S15.typeII_overNormalizer_frobenius_of_c_eq_one_and_d_eq_one
      _hG hnoV hyp.base hc1 hd1 ⟨tdata⟩ hTII hyp.q_lt_p hNUS (pins := hyp.nuGridSupply)
  exact ⟨⟨typeI_data.L, typeI_data.H, typeI_data.L_maximal, typeI_data.normalizer_U_le_L,
    typeI_data.H_eq_LF, typeI_data, rfl, rfl, typeI_data.complement_card_eq_pq⟩⟩

end OddOrder.Peterfalvi.S16
