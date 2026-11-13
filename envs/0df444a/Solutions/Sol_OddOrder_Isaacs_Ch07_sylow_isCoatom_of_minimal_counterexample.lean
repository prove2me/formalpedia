-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.sylow_isCoatom_of_minimal_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T06:00:05.128208+00:00
-- url     : https://prove2.me/submissions/726ce276-22cf-4fd5-8d0b-2709ff7efdf4

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Mathlib/Subgroup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_SylowMaximal.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.Group
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Span.Basic
import Theorems.Thm_OddOrder_Isaacs_Ch07_oPiCorePrime_subgroup_eq_bot_of_opCore_le
import Theorems.Thm_OddOrder_Isaacs_Ch07_hasNormalPComplement_of_mulEquiv
import Theorems.Thm_OddOrder_Isaacs_Ch07_isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
import Theorems.Thm_OddOrder_Isaacs_Ch07_oPiPrimeCore_eq_bot_of_minimal_counterexample
import Theorems.Thm_OddOrder_Isaacs_Ch07_HasThompsonLocalPComplements_of_subgroup

-- ===== OddOrder/Mathlib/Subgroup.lean =====
namespace Subgroup

variable {G : Type*} [Group G]

open scoped Pointwise

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
theorem card_lt_card_of_ne_top {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have hindex_ne_one : H.index ≠ 1 := fun hidx => hH (Subgroup.index_eq_one.mp hidx)
  have hindex_gt_one : 1 < H.index :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨Subgroup.index_ne_zero_of_finite, hindex_ne_one⟩
  calc
    Nat.card H < Nat.card H * H.index := lt_mul_of_one_lt_right Nat.card_pos hindex_gt_one
    _ = Nat.card G := Subgroup.card_mul_index H

end Subgroup

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped commutatorElement

/-- Normal `p`-complements pass to quotient groups.

This is the "homomorphic images" inheritance used at the start of Isaacs §7C, before
the seven-step minimum-counterexample argument.  The complement is the quotient image
of the upstairs normal complement, and `Sylow.mapSurjective` matches each Sylow
subgroup of the quotient with the image of a Sylow subgroup upstairs. -/
theorem hasNormalPComplement_quotient
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (L : Subgroup G) [L.Normal] :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p (G ⧸ L) := by
  classical
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  let f : G →* G ⧸ L := QuotientGroup.mk' L
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective L
  refine ⟨N.map f, Subgroup.Normal.map hN_normal f hf_surj, fun Qbar => ?_⟩
  obtain ⟨Q, hQ_mapSurj⟩ := Sylow.mapSurjective_surjective (p := p) hf_surj Qbar
  have hQ_map : (Q : Subgroup G).map f = (Qbar : Subgroup (G ⧸ L)) := by
    have h := congrArg (fun R : Sylow p (G ⧸ L) => (R : Subgroup (G ⧸ L))) hQ_mapSurj
    simpa [f, Sylow.coe_mapSurjective] using h
  have hQ_compl : Subgroup.IsComplement' N (Q : Subgroup G) := hN_compl Q
  have hp_ndvd_N : ¬ p ∣ Nat.card N := by
    rw [← hQ_compl.index_eq_card]
    exact Q.not_dvd_index
  obtain ⟨k, hQ_card⟩ : ∃ k, Nat.card (Q : Subgroup G) = p ^ k :=
    IsPGroup.iff_card.mp Q.isPGroup'
  have h_coprime : Nat.Coprime (Nat.card N) (Nat.card (Q : Subgroup G)) := by
    rw [hQ_card]
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_ndvd_N).symm).pow_right k
  have h_image_compl :
      Subgroup.IsComplement' (N.map f) ((Q : Subgroup G).map f) :=
    hQ_compl.map_mk' h_coprime L
  rwa [hQ_map] at h_image_compl

/-- Normal `p`-complements pass to homomorphic images of subgroups.

This is the subgroup-image form of the inheritance principle quoted in Isaacs §7C.
It will be used for quotient images of `N_G(X)` and `C_G(X)` in Steps 2 and 3. -/
theorem hasNormalPComplement_subgroup_map
    {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (φ : G →* K) (H : Subgroup G)
    (hH : OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥H) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥(H.map φ) := by
  classical
  let φH : ↥H →* K := φ.comp H.subtype
  have hQuot : OddOrder.Isaacs.Ch05.HasNormalPComplement p (↥H ⧸ φH.ker) :=
    hasNormalPComplement_quotient (G := ↥H) hH φH.ker
  have hRange : OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥φH.range :=
    hasNormalPComplement_of_mulEquiv (QuotientGroup.quotientKerEquivRange φH) hQuot
  have hRange_eq : φH.range = H.map φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.property, rfl⟩
    · rintro ⟨x, hxH, rfl⟩
      exact ⟨⟨x, hxH⟩, rfl⟩
  exact hasNormalPComplement_of_mulEquiv (MulEquiv.subgroupCongr hRange_eq) hRange

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section QuotientCenter

/-- Centers commute with a homomorphism that is injective on the subgroup in question.

This restricted-injectivity form applies both to embeddings into an ambient group and
to quotient maps whose kernel is disjoint from a `p`-subgroup. -/
theorem center_map_subtype_map_of_restrict_injective
    {H : Type*} [Group H] (f : G →* H) {P : Subgroup G}
    (hf : Function.Injective (f.comp P.subtype)) :
    (Subgroup.center ↥(P.map f)).map (P.map f).subtype =
      ((Subgroup.center ↥P).map P.subtype).map f := by
  ext x
  constructor
  · intro hx
    have hx_center := Subgroup.mem_center_map_subtype_iff.mp hx
    obtain ⟨z, hzP, hzx⟩ := hx_center.1
    refine ⟨z, Subgroup.mem_center_map_subtype_iff.mpr ⟨hzP, ?_⟩, hzx⟩
    intro w hw
    have hcomm_f := hx_center.2 (f w) ⟨w, hw, rfl⟩
    rw [← hzx] at hcomm_f
    have hsub :
        (f.comp P.subtype) (⟨w, hw⟩ * ⟨z, hzP⟩) =
          (f.comp P.subtype) (⟨z, hzP⟩ * ⟨w, hw⟩) := by
      change f (w * z) = f (z * w)
      simpa only [map_mul] using hcomm_f
    exact congrArg Subtype.val (hf hsub)
  · rintro ⟨z, hz, rfl⟩
    have hz_center := Subgroup.mem_center_map_subtype_iff.mp hz
    apply Subgroup.mem_center_map_subtype_iff.mpr
    refine ⟨⟨z, hz_center.1, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simpa only [map_mul] using congrArg f (hz_center.2 w hw)

end QuotientCenter

section LocalHypothesisTransport

/-- The two local normal-complement hypotheses are invariant under a group
isomorphism. -/
theorem HasThompsonLocalPComplements.map_mulEquiv
    {H : Type*} [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : HasThompsonLocalPComplements p P) (e : G ≃* H) :
    HasThompsonLocalPComplements p (P.map e.toMonoidHom) := by
  have heP : Function.Injective (e.toMonoidHom.comp P.subtype) :=
    e.injective.comp P.subtype_injective
  have hCenter :
      (Subgroup.center ↥(P.map e.toMonoidHom)).map
          (P.map e.toMonoidHom).subtype =
        ((Subgroup.center ↥P).map P.subtype).map e.toMonoidHom :=
    center_map_subtype_map_of_restrict_injective e.toMonoidHom heP
  constructor
  · have hImage :=
      hasNormalPComplement_subgroup_map e.toMonoidHom
        (Subgroup.centralizer
          (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)) hP.1
    have hLocalizer :
        (Subgroup.centralizer
            (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)).map
              e.toMonoidHom =
          Subgroup.centralizer
            (((Subgroup.center ↥(P.map e.toMonoidHom)).map
              (P.map e.toMonoidHom).subtype : Subgroup H) : Set H) := by
      rw [hCenter]
      simpa only [Subgroup.coe_map] using
        (Subgroup.map_centralizer_eq_of_bijective
          (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)
          e.toMonoidHom e.bijective)
    exact hasNormalPComplement_of_mulEquiv
      (MulEquiv.subgroupCongr hLocalizer) hImage
  · have hImage :=
      hasNormalPComplement_subgroup_map e.toMonoidHom
        (Subgroup.normalizer ((Subgroup.thompsonJ P p : Subgroup G) : Set G)) hP.2
    have hJ :
        Subgroup.thompsonJ (P.map e.toMonoidHom) p =
          (Subgroup.thompsonJ P p).map e.toMonoidHom :=
      Subgroup.thompsonJ_map_of_injective e.injective P p
    have hLocalizer :
        (Subgroup.normalizer
            ((Subgroup.thompsonJ P p : Subgroup G) : Set G)).map e.toMonoidHom =
          Subgroup.normalizer
            ((Subgroup.thompsonJ (P.map e.toMonoidHom) p : Subgroup H) : Set H) := by
      rw [hJ]
      exact Subgroup.map_normalizer_eq_of_bijective _ e.bijective
    exact hasNormalPComplement_of_mulEquiv
      (MulEquiv.subgroupCongr hLocalizer) hImage

/-- Local normal-complement hypotheses at one Sylow subgroup propagate to all
Sylow subgroups by conjugacy. -/
theorem HasThompsonLocalPComplements.of_sylow
    [Finite G] {p : ℕ} [Fact p.Prime] (P Q : Sylow p G)
    (hP : HasThompsonLocalPComplements p (P : Subgroup G)) :
    HasThompsonLocalPComplements p (Q : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hmap :
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom = (Q : Subgroup G) := by
    change (MulAut.conj g • (P : Subgroup G)) = (Q : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  have h := hP.map_mulEquiv (MulAut.conj g)
  rw [hmap] at h
  exact h

/-- The textbook hypotheses at a chosen Sylow subgroup are equivalent to their
intrinsic all-Sylow form. -/
theorem hasThompsonPComplementHypothesis_iff
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    HasThompsonPComplementHypothesis p G ↔
      HasThompsonLocalPComplements p (P : Subgroup G) := by
  constructor
  · exact fun h => h P
  · intro h Q
    exact h.of_sylow P Q

end LocalHypothesisTransport

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_SylowMaximal.lean =====
namespace OddOrder.Isaacs.Ch07

variable {G : Type*} [Group G]

section MinimalCounterexampleStepFour

/-- A finite group whose Sylow `p`-subgroup is the whole group has the trivial
subgroup as a normal `p`-complement. -/
theorem hasNormalPComplement_of_sylow_eq_top
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : (P : Subgroup G) = ⊤) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  refine ⟨⊥, inferInstance, fun Q => ?_⟩
  have hQP : (Q : Subgroup G) = (P : Subgroup G) :=
    (Q.is_maximal' P.isPGroup' (by rw [hP]; exact le_top)).symm
  rw [hQP, hP]
  exact Subgroup.isComplement'_bot_top

/-- **Isaacs Theorem 7.1, Step 4.**

In a minimal counterexample, a Sylow `p`-subgroup `P` is maximal in `G`.
For `P ≤ H < G`, the two Thompson local hypotheses descend to `H`, so
minimality supplies a normal `p`-complement `K ◁ H`.  Step 2 makes `G`
`p`-separable and Step 3 gives `O_{p'}(G) = 1`; the Hall–Higman argument then
gives `O_{p'}(H) = 1`.  Since `K` is a normal `p'`-subgroup, `K = 1`, hence
`H` is a `p`-group and Sylow maximality forces `H = P`. -/
theorem _root_.solution.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (hQuotient : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :
    IsCoatom (P : Subgroup G) := by
  classical
  have hP_ne_top : (P : Subgroup G) ≠ ⊤ := by
    intro hP_top
    exact hG (hasNormalPComplement_of_sylow_eq_top P hP_top)
  let h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G :=
    isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
      (OddOrder.Isaacs.Ch01.opCore_isPGroup p G) hQuotient
  have hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥ :=
    oPiPrimeCore_eq_bot_of_minimal_counterexample P hHyp ih hG
  rw [isCoatom_iff_ge_of_le]
  refine ⟨hP_ne_top, ?_⟩
  intro H hH_ne_top hPH
  have hOp_le_H : OddOrder.Isaacs.Ch01.opCore p G ≤ H :=
    (OddOrder.Isaacs.Ch01.opCore_le P).trans hPH
  have hH_oPiPrime :
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) = ⊥ :=
    oPiCorePrime_subgroup_eq_bot_of_opCore_le hOp' hOp_le_H
  have hPsub_p : IsPGroup p ↥((P : Subgroup G).subgroupOf H) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv]
      exact hn)
  have hPsub_index : ¬ p ∣ ((P : Subgroup G).subgroupOf H).index :=
    fun hp => P.not_dvd_index
      (hp.trans (Subgroup.relIndex_dvd_index_of_le hPH))
  let S : Sylow p ↥H := hPsub_p.toSylow hPsub_index
  have hS_coe :
      (S : Subgroup ↥H) = (P : Subgroup G).subgroupOf H :=
    hPsub_p.toSylow_coe hPsub_index
  have hS_map : (S : Subgroup ↥H).map H.subtype = (P : Subgroup G) := by
    rw [hS_coe, Subgroup.map_subgroupOf_eq_of_le hPH]
  have hH_hyp : HasThompsonPComplementHypothesis p ↥H := by
    rw [hasThompsonPComplementHypothesis_iff S]
    apply HasThompsonLocalPComplements.of_subgroup (G := G) H
    rw [hS_map]
    exact hHyp P
  have hH_card : Nat.card ↥H < Nat.card G :=
    Subgroup.card_lt_card_of_ne_top hH_ne_top
  obtain ⟨K, hK_normal, hK_complement⟩ := ih ↥H hH_card hH_hyp
  let : K.Normal := hK_normal
  have hK_card : Nat.card K = (S : Subgroup ↥H).index :=
    ((hK_complement S).index_eq_card).symm
  have hK_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} K := by
    intro q hq
    rw [hK_card] at hq
    intro hqp
    subst q
    exact S.not_dvd_index (Nat.dvd_of_mem_primeFactors hq)
  have hK_le_core :
      K ≤ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) :=
    hK_pi'.le_oPiCore
  have hK_bot : K = ⊥ := by
    rw [hH_oPiPrime] at hK_le_core
    exact le_bot_iff.mp hK_le_core
  have hS_top : (S : Subgroup ↥H) = ⊤ := by
    have hKS := hK_complement S
    rw [hK_bot] at hKS
    exact Subgroup.isComplement'_bot_left.mp hKS
  have hHP : H ≤ (P : Subgroup G) := by
    rw [← Subgroup.subgroupOf_eq_top, ← hS_coe]
    exact hS_top
  exact hHP

end MinimalCounterexampleStepFour

end OddOrder.Isaacs.Ch07
