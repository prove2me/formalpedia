-- Prove2me | solution 1 for OddOrder.Peterfalvi.S14.exists_typeICovering
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:41:50.01887+00:00
-- url     : https://prove2.me/submissions/2ee15593-fe5b-4a30-b306-a947de344270

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/Conjugacy145C.lean
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/Theorem152Helpers.lean
--   OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean
--   OddOrder/Peterfalvi/S14_MaximalI/TypeICovering.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_TypeICovering

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

section

namespace IsFrobeniusGroup

variable {G : Type*} [Group G] {N A : Subgroup G}

open scoped Pointwise

/-- **A normal `p`-subgroup of a Frobenius group lies in the kernel.**  If `p ∣ |N|` then
`p ∤ |A| = [G : N]` (Lemma 6.1 coprimality), so the image of `P` in `G ⧸ N` is a `p`-group of
`p'`-order, trivial.  If `p ∤ |N|` the order coprimality kills `P ⊓ N`, so `P` and `N` commute
elementwise (the commutator of two normal subgroups lies in their intersection) and
`P ≤ C_G(n₀) ≤ N` for any `1 ≠ n₀ ∈ N` (Thm 6.4 (1) ⇒ (4)). -/
theorem normal_pGroup_le_kernel [Finite G] (h : IsFrobeniusGroup G N A)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} [P.Normal] (hP : IsPGroup p ↥P) : P ≤ N := by
  classical
  have : N.Normal := h.isNormal
  by_cases hpN : p ∣ Nat.card ↥N
  · have hpA : ¬ p ∣ Nat.card ↥A :=
      (Nat.Prime.coprime_iff_not_dvd Fact.out).mp
        (Nat.Coprime.coprime_dvd_left hpN h.coprime_card_kernel_complement)
    have himg : IsPGroup p ↥(P.map (QuotientGroup.mk' N)) := hP.map _
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp himg
    have hdvd : Nat.card ↥(P.map (QuotientGroup.mk' N)) ∣ Nat.card ↥A := by
      have h1 : Nat.card ↥(P.map (QuotientGroup.mk' N)) ∣ Nat.card (G ⧸ N) :=
        Subgroup.card_subgroup_dvd_card _
      rwa [← Subgroup.index_eq_card, h.isComplement.symm.index_eq_card] at h1
    have hk0 : k = 0 := by
      by_contra hk0
      exact hpA (dvd_trans (dvd_pow_self p hk0) (hk ▸ hdvd))
    have hbot : P.map (QuotientGroup.mk' N) = ⊥ :=
      Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])
    have hle := (Subgroup.map_eq_bot_iff _).mp hbot
    rwa [QuotientGroup.ker_mk'] at hle
  · have hPN : P ⊓ N = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨k, hk⟩ := hP ⟨x, (Subgroup.mem_inf.mp hx).1⟩
      have hxpk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hordp : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxpk
      have hordN : orderOf x ∣ Nat.card ↥N :=
        Subgroup.orderOf_dvd_natCard N (Subgroup.mem_inf.mp hx).2
      have hcop : Nat.gcd (p ^ k) (Nat.card ↥N) = 1 :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN)
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hordp hordN))
    obtain ⟨n₀, hn₀N, hn₀1⟩ :=
      (Subgroup.nontrivial_iff_exists_ne_one N).mp
        ((Subgroup.nontrivial_iff_ne_bot N).mpr h.ne_bot_kernel)
    refine le_trans ?_ (h.centralizer_kernel_le n₀ hn₀N hn₀1)
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc1 : f * n₀ * f⁻¹ * n₀⁻¹ ∈ N :=
      mul_mem (h.isNormal.conj_mem n₀ hn₀N f) (inv_mem hn₀N)
    have hc2 : f * n₀ * f⁻¹ * n₀⁻¹ ∈ P := by
      have hconj : n₀ * f⁻¹ * n₀⁻¹ ∈ P := ‹P.Normal›.conj_mem f⁻¹ (inv_mem hf) n₀
      simpa [mul_assoc] using mul_mem hf hconj
    have hcomm : f * n₀ * f⁻¹ * n₀⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hPN ▸ Subgroup.mem_inf.mpr ⟨hc2, hc1⟩)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hcomm
    exact hcomm

/-- **The Fitting subgroup of a Frobenius group lies in the kernel**: each `O_p(G)` is a
normal `p`-subgroup, hence in `N` (`normal_pGroup_le_kernel`), and `F(G) = ⨆ p, O_p(G)`. -/
theorem fitting_le_kernel [Finite G] (h : IsFrobeniusGroup G N A) :
    OddOrder.Isaacs.Ch01.fitting G ≤ N := by
  refine iSup_le fun p => ?_
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact h.normal_pGroup_le_kernel (OddOrder.Isaacs.Ch01.opCore_isPGroup p G)

end IsFrobeniusGroup

end

end OddOrder.Isaacs.Ch06

-- ===== OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/Conjugacy145C.lean =====
namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Easy half of the `M̃` cover** (`M_σ^# ⊆ M̃`): every `σ`-length-one element `x ∈ M_σ^#` lies in
`M̃` via the trivial decomposition `x = x · 1` (`1 ∈ R(x)`).  This is the `ℓ_σ = 1` part of the
faithful covering (BG Cor 14.9); the `ℓ_σ = 2` twisted elements need the signalizer capture
(Lemma 14.6). -/
theorem sigmaSharp_subset_Mtilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} :
    sigmaSharp M ⊆ Mtilde hG D M :=
  fun g hg => ⟨g, hg, 1, Subgroup.one_mem _, (mul_one g).symm⟩

end OddOrder.BG.Ch4.S14

-- ===== OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/Theorem152Helpers.lean =====
namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **General helper (§14-independent, reusable).**  A nonidentity maximal subgroup of a minimal
simple group is self-normalizing: `N_G(M) = M`.  If `M ⊊ N_G(M)`, maximality forces `N_G(M) = G`,
so `M ⊴ G`; simplicity then gives `M = ⊥` or `M = ⊤`, both excluded.  This is the step of BG
Corollary 15.3(b) that turns `M^{gc} = M` into `gc ∈ M`. -/
theorem normalizer_eq_self_of_mem_maximalSubgroups [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMne : M ≠ ⊥) :
    Subgroup.normalizer M = M := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with heq | hlt
  · exact le_of_eq heq.symm
  · have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp
      ((mem_maximalSubgroups.mp hM).2 _ hlt)
    rcases hG.simple.eq_bot_or_eq_top_of_normal M hnorm with hbot | htop
    · exact absurd hbot hMne
    · exact absurd htop (mem_maximalSubgroups.mp hM).1

end OddOrder.BG.Ch4.S15

-- ===== OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean =====
namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`𝓜_σ(x)` is a singleton when the centralizer does not escape** (the no-escaping
degeneration of BG Theorem 14.4): if `M, L ∈ 𝓜_σ(x)` and `C_G(x) ≤ M`, then `M = L`.  For
`x ∈ M_σ` the σ-length is `1` (`length_one_of_isPiElement_sigma`), so in the multi-maximal case
the Theorem-14.4 sharp transitivity of `R(x) ≤ C_G(x)` on `𝓜_σ(x)` yields `r ∈ R(x) ≤ M`
conjugating `M` onto the *different* member `L`, absurd for `r ∈ M`.

This is the uniqueness input of the all-type-I `FittingIsTI` derivation (Peterfalvi (8.13.c1)
degeneration, `S14.allTypeI_fittingIsTI`): `x ∈ M_σ# ∩ (M^g)_σ#` with non-escaping centralizers
forces `M^g = M`, i.e. `g ∈ N_G(M) = M`. -/
theorem eq_of_mem_maximalSigmaSubgroupsOfElement_of_centralizer_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : OddOrder.BG.Ch4.S14.SigmaDecompositionData G) {x : G} (hx1 : x ≠ 1)
    {M L : Subgroup G}
    (hM : M ∈ OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x)
    (hL : L ∈ OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x)
    (hc : Subgroup.centralizer ({x} : Set G) ≤ M) :
    M = L := by
  classical
  by_contra hML
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hlen : D.length x = 1 :=
    OddOrder.BG.Ch4.S14.length_one_of_isPiElement_sigma hG D hM.1 hx1
      (OddOrder.BG.Ch4.S14.isPiElement_sigma_of_mem_Msigma hM.2)
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x).ncard :=
    Set.one_lt_ncard_iff_nontrivial.mpr ⟨M, hM, L, hL, hML⟩
  -- the Theorem-14.4 sharp transitivity of `R(x)` on `𝓜_σ(x)`, at the pair `(M, L)`
  obtain ⟨N, hNspec, -⟩ :=
    (OddOrder.BG.Ch4.S14.sigmaLength_one_centralizer_structure hG D hx1 hlen).2 hgt
  obtain ⟨r, ⟨hrmem, hrconj⟩, -⟩ := (hNspec.2.2.2.2.2.2 M hM).2.2.2 L hL
  have hrM : r ∈ M := hc (Subgroup.mem_inf.mp hrmem).2
  exact hML ((hrconj.symm.trans
    (conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hrM))).symm)

/-- **`R(x)` collapses when the centralizer does not escape** (the (12.17)-side degeneration of
BG Theorem 14.4): if `M ∈ 𝓜_σ(x)` and `C_G(x) ≤ M`, then `R(x) = 1` — the `ncard`-form
corollary of the singleton fact `eq_of_mem_maximalSigmaSubgroupsOfElement_of_centralizer_le`. -/
theorem Rsub_eq_bot_of_centralizer_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : OddOrder.BG.Ch4.S14.SigmaDecompositionData G) {x : G} {M : Subgroup G}
    (hM : M ∈ OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x)
    (hc : Subgroup.centralizer ({x} : Set G) ≤ M) :
    OddOrder.BG.Ch4.S14.Rsub hG D x = ⊥ := by
  classical
  have hnot : ¬ (x ≠ 1 ∧ D.length x = 1 ∧
      1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x).ncard) := by
    rintro ⟨hx1, -, hgt⟩
    have : Finite (Subgroup G) :=
      Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
    have hnt : (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x).Nontrivial :=
      Set.one_lt_ncard_iff_nontrivial.mp hgt
    obtain ⟨L, hL, hLM⟩ := hnt.exists_ne M
    exact hLM (eq_of_mem_maximalSigmaSubgroupsOfElement_of_centralizer_le hG D hx1
      hM hL hc).symm
  rw [OddOrder.BG.Ch4.S14.Rsub, dif_neg hnot]

/-- **The no-escaping collapse `M̃ = M_σ#`** (the (12.17)-case degeneration of the faithful BG
Theorem E cover): if no centralizer of an `M_σ#`-element escapes `M`, every signalizer `R(x)`
is trivial and the thickened `M̃ = ⋃_{x ∈ M_σ#} x·R(x)` collapses onto `M_σ#`. -/
theorem Mtilde_eq_sigmaSharp_of_forall_centralizer_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : OddOrder.BG.Ch4.S14.SigmaDecompositionData G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hesc : ∀ x ∈ OddOrder.BG.Ch4.S14.sigmaSharp M,
      Subgroup.centralizer ({x} : Set G) ≤ M) :
    OddOrder.BG.Ch4.S14.Mtilde hG D M = OddOrder.BG.Ch4.S14.sigmaSharp M := by
  refine Set.Subset.antisymm ?_ (OddOrder.BG.Ch4.S14.sigmaSharp_subset_Mtilde hG D)
  rintro g ⟨x, hx, x', hx', rfl⟩
  have hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    have hx0 := hx
    rw [OddOrder.BG.Ch4.S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe] at hx0
    exact hx0.1
  have hbot := Rsub_eq_bot_of_centralizer_le hG D ⟨hM, hxM⟩ (hesc x hx)
  rw [hbot, Subgroup.mem_bot] at hx'
  rwa [hx', mul_one]

end OddOrder.Peterfalvi.S10

-- ===== OddOrder/Peterfalvi/S14_MaximalI/TypeICovering.lean =====
namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section Theorem1217

variable [Finite G]

/-- **Peterfalvi (8.8.a) dichotomy, all-type-I case** — the case-(b) covering branch of BG Theorem
E cannot occur when every maximal subgroup is of type I.

The case-(b) branch of `S10.bgTheoremE_cover_data` carries its type-`P` provenance
(`maximalTypePFamily G` nonempty — the (8.8.a) *exclusivity*: the two-exceptional-subgroup cover
is produced, in `nonTypeICovering_of_isTypeP`, *only* from a reference type-`P` maximal).  A
type-`P` maximal is type F-negated (`isTypeF_iff_not_isTypeP`), while `hall` makes it type I
= type F (Proposition 16.1(a), `proposition_type_classification`) — contradiction.

The provenance hypothesis is essential: the bare `BGTheoremENonTypeICovering` carrier records
only the exceptional `Ẑ`-set and its cover geometry, and an **empty** exceptional set satisfies
it whenever the type-I cover holds — so no contradiction with `hall` is extractable from the
carrier alone, and the earlier `(hcov : BGTheoremENonTypeICovering data)`-form of this lemma was
provable only through the full (12.17) contradiction (circular here). -/
private theorem not_nonTypeICovering_of_all_typeI (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hP : (OddOrder.BG.Ch4.S14.maximalTypePFamily G).Nonempty)
    (hall : ∀ N : Subgroup G, N ∈ maximalSubgroups G → IsTypeI N) :
    False := by
  obtain ⟨Mref, hMrefmax, hMrefP⟩ := hP
  exact OddOrder.BG.Ch4.S14.isTypeF_iff_not_isTypeP.mp
    ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hMrefmax).1.mp
      (hall Mref hMrefmax)) hMrefP

/-- **A type-I maximal has no "hat" beyond its kernel** (the (12.17)-side collapse of the (8.14)
signalizer support): for a type-I maximal `N`, every element of `N` whose `N_σ`-centralizer is
nontrivial already lies in `N_σ`.

By (12.7) (`typeI_frobenius`) `N` is a Frobenius group with kernel `N_F = N_σ`
(`maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2`), and the centralizer of a nonidentity
kernel element is contained in the kernel (Isaacs Thm 6.4 (1) ⇒ (4),
`IsFrobeniusGroup.centralizer_kernel_le`); so `x ∈ N` centralizing some `1 ≠ r ∈ N_σ` lies in
`N_σ`. -/
private theorem typeI_hatMsigma_subset_Msigma (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {N : Subgroup G} (hNmax : N ∈ maximalSubgroups G) (hNI : IsTypeI N) :
    OddOrder.BG.Ch4.S16.hatMsigma N ⊆ (OddOrder.BG.Ch3.S10.Msigma N : Set G) := by
  rintro x ⟨hxN, hRne⟩
  -- a nonidentity element `r` of `N_σ ⊓ C_G(x)`
  have hr : ∃ r ∈ OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G), r ≠ 1 := by
    by_contra h
    push Not at h
    exact hRne (Subgroup.eq_bot_iff_forall _ |>.mpr h)
  obtain ⟨r, hr, hr1⟩ := hr
  have hrσ : r ∈ OddOrder.BG.Ch3.S10.Msigma N := (Subgroup.mem_inf.mp hr).1
  have hrC : r ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hr).2
  have hrN : r ∈ N := OddOrder.BG.Ch3.S10.Msigma_le N hrσ
  -- `N` is Frobenius with kernel `typeF.H = N_F = N_σ` ((12.7)).
  obtain ⟨fd, -⟩ := typeI_frobenius hG hnoV hNmax hNI
  have hHσ : fd.typeI.typeF.H = OddOrder.BG.Ch3.S10.Msigma N := by
    rw [fd.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2 hG hNmax
      (Or.inl ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hNmax).1.mp hNI))
  have hrH : r ∈ fd.typeI.typeF.H := by rw [hHσ]; exact hrσ
  -- inside `↥N`: `x` centralizes the nonidentity kernel element `r`, so `x` is in the kernel.
  have hcent := fd.frobenius.centralizer_kernel_le ⟨r, hrN⟩ (Subgroup.mem_subgroupOf.mpr hrH)
    (fun h => hr1 (Subtype.ext_iff.mp h))
  have hxbar : (⟨x, hxN⟩ : ↥N) ∈ Subgroup.centralizer ({(⟨r, hrN⟩ : ↥N)} : Set ↥N) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hrC).symm
  have hxH : x ∈ fd.typeI.typeF.H := Subgroup.mem_subgroupOf.mp (hcent hxbar)
  rw [hHσ] at hxH
  exact hxH

/-- **Peterfalvi (12.17), the no-escaping control**: in the all-type-I configuration, no
centralizer of an `M_σ#`-element escapes `M`.

An escape produces the BG Theorem D(4) neighbour `N` (`exists_RData_escape_structure`, the
sorry-free escape structure of Theorem D) with `x ∈ Â_σ(N) ∖ N_σ`; but `N` is type I (`hall`),
so `Â_σ(N) ⊆ N_σ` (`typeI_hatMsigma_subset_Msigma`) — contradiction.  This is the exact
hypothesis under which the faithful BG Theorem E cover collapses onto the Frobenius kernels
(`Mtilde_eq_sigmaSharp_of_forall_centralizer_le`, issue 9080). -/
private theorem allTypeI_centralizer_le (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hall : ∀ N : Subgroup G, N ∈ maximalSubgroups G → IsTypeI N)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∀ x ∈ OddOrder.BG.Ch4.S14.sigmaSharp M, Subgroup.centralizer ({x} : Set G) ≤ M := by
  intro x hx
  by_contra hesc
  obtain ⟨R, -, N, ⟨hNmem, -, -, hxA, -, -, -⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.exists_RData_escape_structure hG hM hx hesc
  exact hxA.2 (typeI_hatMsigma_subset_Msigma hG hnoV hNmem.1 (hall N hNmem.1) hxA.1.1)

set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (8.13.c1)+(2.3), all-type-I case** — the escaping-centralizer control makes
each type-I kernel's Fitting subgroup a `TI`-subgroup, supplying the `FittingIsTI` gate of the
(12.17) `isTI` covering input.

For a maximal subgroup `M` of a minimal simple group of odd order in which **every** maximal
subgroup is of type I (`hall`), the Fitting subgroup `F(M)` is `TI` (`S15.FittingIsTI M`):
`M` is type F, so `M_F = M_σ`, and the (12.7) Frobenius structure pins `F(M) ≤ M_F`
(`IsFrobeniusGroup.fitting_le_kernel`); for `a, g·a·g⁻¹ ∈ F(M)^# ⊆ M_σ^#` the non-escaping
control (`allTypeI_centralizer_le`) gives `C_G(g·a·g⁻¹) ≤ M`, and the Theorem-14.4 σ-uniqueness
(`S10.eq_of_mem_maximalSigmaSubgroupsOfElement_of_centralizer_le`) pins `M = M^g`, i.e.
`g ∈ N_G(M) = M = N_G(F(M))`.  The type-V exclusion feeding (12.7) is discharged internally by
the axiom-clean (10.10) `no_typeV_maximal_unconditional`.

**Soundness**: the statement is *not* claimed for an arbitrary type-I subgroup — the
(12.10)/(12.16) Frobenius witness `L` is type-I-like yet has `H^# = (L_F)#` **not** `TI` in `G`
(Pf (12.10), see `sibleyTarget_frobI`); the ambient all-type-I hypothesis `hall` (through the
non-escaping control) is what excludes that configuration. -/
private theorem allTypeI_fittingIsTI (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hI : IsTypeI M)
    (hall : ∀ N : Subgroup G, N ∈ maximalSubgroups G → IsTypeI N) :
    OddOrder.BG.Ch4.S15.FittingIsTI M := by
  classical
  have hnoV : ¬ ∃ L : Subgroup G, L ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV L :=
    OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG
  -- Type F, so `M_F = M_σ`.
  have htypeF : OddOrder.BG.Ch4.S14.IsTypeF M :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).1.mp hI
  have hMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2 hG hM
      (Or.inl htypeF)
  -- (12.7): `M` is Frobenius with kernel `M_F`, so `F(M) ≤ M_F = M_σ`.
  obtain ⟨fdata, -⟩ := typeI_frobenius hG hnoV hM hI
  have hfitle : OddOrder.BG.Ch4.S15.fittingInAmbient M ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    have h1 : OddOrder.Isaacs.Ch01.fitting ↥M ≤ fdata.typeI.typeF.H.subgroupOf M :=
      fdata.frobenius.fitting_le_kernel
    have h2 := Subgroup.map_mono (f := M.subtype) h1
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr fdata.typeI.typeF.H_le,
      fdata.typeI.typeF.H_eq, hMσ] at h2
    exact h2
  -- TI: a nonidentity conjugate meeting `F(M)#` pins the maximal subgroup.
  intro g hg
  obtain ⟨a, ha, hga⟩ := hg
  have hx1 : g * a * g⁻¹ ≠ 1 := fun h => hga.2 (Set.mem_singleton_iff.mpr h)
  have haσ : a ∈ OddOrder.BG.Ch3.S10.Msigma M := hfitle (SetLike.mem_coe.mp ha.1)
  have hxσ : g * a * g⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := hfitle (SetLike.mem_coe.mp hga.1)
  -- `x = g·a·g⁻¹ ∈ (M^g)_σ` as well.
  have hM'max : MulAut.conj g • M ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr
      (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hM))
  have hxσ' : g * a * g⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • M) := by
    rw [OddOrder.BG.Ch4.S14.Msigma_conj_smul, Subgroup.pointwise_smul_def, Subgroup.mem_map]
    exact ⟨a, haσ, rfl⟩
  -- Non-escaping centralizer at `M` + Theorem-14.4 σ-uniqueness pin `M = M^g`.
  have hcM : Subgroup.centralizer ({g * a * g⁻¹} : Set G) ≤ M := by
    refine allTypeI_centralizer_le hG hnoV hall hM _ ?_
    rw [OddOrder.BG.Ch4.S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff]
    exact ⟨SetLike.mem_coe.mpr hxσ, fun h => hx1 (Set.mem_singleton_iff.mp h)⟩
  have heq : M = MulAut.conj g • M :=
    OddOrder.Peterfalvi.S10.eq_of_mem_maximalSigmaSubgroupsOfElement_of_centralizer_le hG
      (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG) hx1
      ⟨hM, hxσ⟩ ⟨hM'max, hxσ'⟩ hcM
  -- `g ∈ N_G(M) = M = N_G(F(M))`.
  have hMne : M ≠ ⊥ := fun h =>
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
      (le_bot_iff.mp (h ▸ OddOrder.BG.Ch3.S10.Msigma_le M))
  have hgM : g ∈ M := by
    have hgN : g ∈ Subgroup.normalizer M :=
      OddOrder.GroupTheory.mem_normalizer_of_conj_smul_eq_self heq.symm
    rwa [OddOrder.BG.Ch4.S15.normalizer_eq_self_of_mem_maximalSubgroups hG hM hMne] at hgN
  rw [OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hM]
  exact hgM

/-- **Peterfalvi (8.17)/(8.13.c1), all-type-I case**: the §8 covering inputs of (12.17) exist.

Built as an honest reduction from BG Theorem E (`S10.bgTheoremE_cover_data`): in the all-type-I case
every representative `M_i` has `data.tau i = .I` (type exclusivity, `not_isTypeI_of_isTypeNonI`), so
`mainSubgroup (M_i) (τ_i) = (M_i)_F`.  The `reps`/`reps_maximal` plumbing, `coprime` (the (8.17)
prime-factor partition is disjoint, hence the kernels are coprime), `two_le` (a single class would
make `|G#| = (|M_s|-1)|G:M| < |G|-1 = |G#|`), and `covers` (the (12.17)-faithful collapse, issue
9080: no centralizer escapes by (12.7)+Theorem D(4) (`allTypeI_centralizer_le`), so the faithful
BG Cor 14.9 cover collapses onto the kernels, `Mtilde_eq_sigmaSharp_of_forall_centralizer_le`) are
all discharged.  The two formerly-sorried inputs are also discharged: `isTI` by the
escaping-centralizer control (8.13.c1)+(2.3) (`allTypeI_fittingIsTI`), and the selection of the
type-I cover branch under `hall` by the type-`P` provenance of the case-(b) branch
(`not_nonTypeICovering_of_all_typeI`, the (8.8.a) exclusivity). -/
theorem _root_.solution (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) :
    Nonempty (TypeICovering hG hall) := by
  classical
  -- `BGTheoremECoverData.ι : Type*` is universe-polymorphic; pin the index type to `Type 0`.
  obtain ⟨data, hcover⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  have : Fintype data.ι := data.finite_index
  -- **Every representative is type I**, so `data.tau i = .I` and hence
  -- `mainSubgroup (M_i) (τ_i) = (M_i)_F`.  Type exclusivity is
  -- `not_isTypeI_of_isTypeNonI` (BG §16): a type-`P` (= non-type-I) maximal is not type I.
  have hMF : ∀ i, mainSubgroup (data.reps i) (data.tau i)
      = maxNilpotentNormalHall (data.reps i) := by
    intro i
    have hI : IsTypeI (data.reps i) := hall _ (data.maximal i)
    have htau := data.typed i
    have htauI : data.tau i = PeterfalviType.I := by
      by_contra hne
      have hNonI : IsTypeNonI (data.reps i) := by
        cases hc : data.tau i with
        | I => exact absurd hc hne
        | II => rw [hc] at htau; exact Or.inl htau
        | III => rw [hc] at htau; exact Or.inr (Or.inl htau)
        | IV => rw [hc] at htau; exact Or.inr (Or.inr (Or.inl htau))
        | V => rw [hc] at htau; exact Or.inr (Or.inr (Or.inr htau))
      exact OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG (data.maximal i) hNonI hI
    simp only [htauI, mainSubgroup]
  -- The `Fin k`-indexing of the representatives (`e : data.ι ≃ Fin k`).
  set e := Fintype.equivFin data.ι with he
  rcases hcover with hTypeI | hNonTypeI
  · -- **(8.8.a) type-I cover branch.**
    refine ⟨{
      k := Fintype.card data.ι
      reps := fun j => data.reps (e.symm j)
      reps_maximal := fun j => data.maximal (e.symm j)
      two_le := ?_
      isTI := ?_
      coprime := ?_
      covers := ?_ }⟩
    · -- **`two_le`** (discharged): at least two conjugacy classes of maximal subgroups (7.10).
      -- A single class would force `|G#| = |thickenedA1(M)| = (|M_s| - 1)|G : M|`; but
      -- `(|M_s| - 1)|G : M| ≤ (|M| - 1)|G : M| = |G| - |G : M| ≤ |G| - 2 < |G| - 1 = |G#|`, and an
      -- empty class would force `|G#| = 0`, both impossible.  No counting of disjoint unions is
      -- needed: a one-element index makes the cover `⋃ᵢ thickenedA1(Mᵢ)` equal to a single
      -- `thickenedA1(M)`, whose cardinality is strictly below `|G#|`.
      have : Nontrivial G := hG.simple.toNontrivial
      by_contra hlt
      rw [Nat.not_le] at hlt
      have hcard01 : Fintype.card data.ι = 0 ∨ Fintype.card data.ι = 1 := by omega
      rcases hcard01 with h0 | h1
      · -- empty index: the cover is empty, but `G#` contains a nonidentity element.
        rw [Fintype.card_eq_zero_iff] at h0
        have hempty : (⋃ i, data.cover i) = ∅ :=
          Set.iUnion_of_empty _
        rw [← hTypeI.cover_nonidentity] at hempty
        obtain ⟨b, hb⟩ := exists_ne (1 : G)
        have hbmem : b ∈ sharpSubgroup (⊤ : Subgroup G) := by
          simp only [sharpSubgroup, Subgroup.coe_top, Set.mem_sdiff, Set.mem_univ, true_and,
            Set.mem_singleton_iff]
          exact hb
        rw [hempty] at hbmem
        exact hbmem.elim
      · -- one class: `⋃ᵢ thickenedA1(Mᵢ) = thickenedA1(M)`, of cardinality `< |G#|`.
        obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp h1
        have hunion : (⋃ i, data.cover i) = data.cover i₀ := by
          ext x
          simp only [Set.mem_iUnion]
          exact ⟨fun ⟨i, hi⟩ => by rwa [hi₀ i] at hi, fun hx => ⟨i₀, hx⟩⟩
        rw [← hTypeI.cover_nonidentity] at hunion
        have hcard_eq : Nat.card ↥(data.cover i₀) = Nat.card G - 1 := by
          rw [Nat.card_coe_set_eq, ← hunion]
          change ((↑(⊤ : Subgroup G) : Set G) \ {1}).ncard = Nat.card G - 1
          rw [Subgroup.coe_top, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ]
        rw [data.cover_card i₀] at hcard_eq
        -- Arithmetic contradiction.
        have hmain_le : mainSubgroup (data.reps i₀) (data.tau i₀) ≤ data.reps i₀ :=
          (hMF i₀).le.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le (data.reps i₀))
        have ham : Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀))
            ≤ Nat.card ↥(data.reps i₀) := Subgroup.card_le_of_le hmain_le
        have hidx0 : (data.reps i₀).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have hidx1 : (data.reps i₀).index ≠ 1 :=
          fun h => (data.maximal i₀).1 (Subgroup.index_eq_one.mp h)
        have hidx : 2 ≤ (data.reps i₀).index := by omega
        have hmidx : Nat.card ↥(data.reps i₀) * (data.reps i₀).index = Nat.card G :=
          Subgroup.card_mul_index (data.reps i₀)
        have hm_pos : 0 < Nat.card ↥(data.reps i₀) := Nat.card_pos
        have hG2 : 2 ≤ Nat.card G :=
          le_trans hidx (hmidx ▸ Nat.le_mul_of_pos_left (data.reps i₀).index hm_pos)
        have hb1 : (Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀)) - 1)
            * (data.reps i₀).index
            ≤ (Nat.card ↥(data.reps i₀) - 1) * (data.reps i₀).index :=
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_right ham 1)
        have hrhs : (Nat.card ↥(data.reps i₀) - 1) * (data.reps i₀).index
            = Nat.card G - (data.reps i₀).index := by rw [Nat.sub_one_mul, hmidx]
        rw [hrhs] at hb1
        -- `hcard_eq : P = |G| - 1`, `hb1 : P ≤ |G| - idx`, `idx ≥ 2`, `|G| ≥ 2` ⟹ `False`.
        set P := (Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀)) - 1)
          * (data.reps i₀).index with hP
        omega
    · -- `isTI`: each kernel sharp-set `((M_i)_F)#` is a TI-subset, by (8.13.c1)+(2.3).
      -- Honest derivation: `FittingIsTI (M_j)` (the (8.13.c1) escaping-centralizer gate,
      -- `allTypeI_fittingIsTI`) feeds `maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`
      -- (S16, `M_F# TI` with normalizer `N_G(M_F)`); and `N_G(M_F) = M_j` for the type-I maximal
      -- (`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`, kernel `≠ ⊥`).
      intro j
      set M := data.reps (e.symm j) with hMdef
      have hMmax : M ∈ maximalSubgroups G := data.maximal (e.symm j)
      have hMI : IsTypeI M := hall _ hMmax
      -- `M_F ≠ ⊥` for the type-I maximal.
      have hMFne : maxNilpotentNormalHall M ≠ ⊥ := by
        obtain ⟨td⟩ := hMI
        rw [← td.typeF.H_eq]
        exact td.typeF.H_nontrivial
      -- `N_G(M_F) = M`.
      have hNorm : M = Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
        maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG hMmax hMFne
      -- `M_F#` is TI with normalizer `N_G(M_F)`, from `FittingIsTI M`; rewrite `N_G(M_F) = M` in
      -- the TI witness (not in the goal — that would fold `M` inside `maxNilpotentNormalHall M`).
      have hTI :=
        OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hMmax
          (allTypeI_fittingIsTI hG hMmax hMI hall)
      rw [← hNorm] at hTI
      -- `sharpSubgroup (maxNilpotentNormalHall M)` unfolds to `(maxNilpotentNormalHall M) \ {1}`.
      exact hTI
    · -- **`coprime`** (discharged): the kernels have pairwise-coprime order because the (8.17)
      -- partition makes their prime-factor sets disjoint.
      intro j j' hjj'
      have hne : e.symm j ≠ e.symm j' := fun h => hjj' (e.symm.injective h)
      have hdisj := data.primeFactors_disjoint (e.symm j) (e.symm j') hne
      simp only [hMF] at hdisj
      have hcard1 : Nat.card ↥(maxNilpotentNormalHall (data.reps (e.symm j))) ≠ 0 :=
        Nat.card_pos.ne'
      have hcard2 : Nat.card ↥(maxNilpotentNormalHall (data.reps (e.symm j'))) ≠ 0 :=
        Nat.card_pos.ne'
      exact (Nat.disjoint_primeFactors hcard1 hcard2).mp hdisj
    · -- **`covers`** (discharged, the (12.17)-faithful route of issue 9080): the faithful BG
      -- cover `𝒞_G(M̃)` (BG Cor 14.9, all-type-`F`) covers `G#`; in the all-type-I case no
      -- centralizer escapes (`allTypeI_centralizer_le`, from (12.7) via Theorem D(4)), so every
      -- signalizer is trivial and `M̃ = M_σ# = (M_F)#`
      -- (`Mtilde_eq_sigmaSharp_of_forall_centralizer_le`); finally the witness maximal is moved
      -- to its conjugacy representative.
      intro x hx1
      have htypeF : ∀ M' ∈ maximalSubgroups G, OddOrder.BG.Ch4.S14.IsTypeF M' := fun M' hM' =>
        (OddOrder.BG.Ch4.S16.proposition_type_classification hG hM').1.mp (hall M' hM')
      have hxsharp : x ∈ sharpSubgroup (⊤ : Subgroup G) := ⟨Subgroup.mem_top x, hx1⟩
      rw [OddOrder.BG.Ch4.S14.sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF hG
        htypeF] at hxsharp
      obtain ⟨M, hMmax, hxM⟩ := Set.mem_iUnion₂.mp hxsharp
      rw [OddOrder.Peterfalvi.S10.Mtilde_eq_sigmaSharp_of_forall_centralizer_le hG _ hMmax
        (allTypeI_centralizer_le hG hnoV hall hMmax)] at hxM
      -- `x = c * t * c⁻¹` with `t ∈ M_σ#`; move `M` to its representative `conj g • M = reps i`.
      obtain ⟨t, ht, c, hc⟩ := hxM
      obtain ⟨i, g, hgconj⟩ := data.representatives M hMmax
      refine ⟨e i, g * c⁻¹, ?_⟩
      have hreps : data.reps (e.symm (e i)) = data.reps i := by rw [Equiv.symm_apply_apply]
      have hyt : (g * c⁻¹) * x * (g * c⁻¹)⁻¹ = g * t * g⁻¹ := by rw [← hc]; group
      rw [hreps, hyt]
      -- `g t g⁻¹ ∈ (conj g • M)_σ# = (reps i)_σ# = ((reps i)_F)#`
      have hmem : g * t * g⁻¹ ∈ MulAut.conj g • OddOrder.BG.Ch4.S14.sigmaSharp M := by
        rw [show g * t * g⁻¹ = MulAut.conj g • t from by
          rw [MulAut.smul_def, MulAut.conj_apply]]
        exact Set.smul_mem_smul_set ht
      rw [OddOrder.BG.Ch4.S14.sigmaSharp_conj_smul, hgconj] at hmem
      have hσeq : OddOrder.BG.Ch4.S14.sigmaSharp (data.reps i)
          = (maxNilpotentNormalHall (data.reps i) : Set G) \ {1} := by
        rw [OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2 hG
          (data.maximal i) (Or.inl (htypeF _ (data.maximal i)))]
        rfl
      rw [← hσeq]
      exact hmem
  · -- **(8.8.b) non-type-I cover branch**: ruled out when every maximal subgroup is type I.
    -- The branch carries its type-`P` provenance (the (8.8.a) exclusivity recorded in
    -- `bgTheoremE_cover_data`), which `hall` contradicts
    -- (`not_nonTypeICovering_of_all_typeI`).
    exact (not_nonTypeICovering_of_all_typeI hG hNonTypeI.1 hall).elim

end Theorem1217

end OddOrder.Peterfalvi.S14
