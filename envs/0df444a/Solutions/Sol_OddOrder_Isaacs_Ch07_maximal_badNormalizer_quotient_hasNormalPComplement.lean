-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.maximal_badNormalizer_quotient_hasNormalPComplement
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:55:57.977501+00:00
-- url     : https://prove2.me/submissions/b611d0a2-5e7c-4cfe-b722-bb630cc381ce

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ThompsonSubgroup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Theorems.Thm_Subgroup_thompsonJ_ne_bot
import Theorems.Thm_OddOrder_Isaacs_Ch07_hasNormalPComplement_of_mulEquiv

-- ===== OddOrder/GroupTheory/ThompsonSubgroup.lean =====
namespace Subgroup

variable {G : Type*} [Group G]

/-- `J(P) ≤ P`: Thompson subgroup は `P` の部分群. -/
theorem thompsonJ_le (P : Subgroup G) (p : ℕ) : thompsonJ P p ≤ P := by
  refine iSup_le fun E => iSup_le fun hE => ?_
  exact hE.1

/-- **Conjugation by a normalizing element fixes `J(P)`**: if `g ∈ N(P)`, then
`g · J(P) · g⁻¹ = J(P)` (as `(thompsonJ P p).map (conj g) = thompsonJ P p`).

`J` commutes with the injective automorphism `conj g` (`thompsonJ_map_of_injective`),
and `g ∈ N(P)` gives `P.map (conj g) = P`. -/
theorem thompsonJ_map_conj_eq_of_mem_normalizer [Finite G] {p : ℕ} {P : Subgroup G}
    {g : G} (hg : g ∈ Subgroup.normalizer P) :
    (thompsonJ P p).map (MulAut.conj g).toMonoidHom = thompsonJ P p := by
  have hg_iff : ∀ n, n ∈ P ↔ g * n * g⁻¹ ∈ P := Subgroup.mem_normalizer_iff.mp hg
  have hP_conj : P.map (MulAut.conj g).toMonoidHom = P := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hg_iff z).mp hz
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · have hmem : g * (g⁻¹ * y * g) * g⁻¹ ∈ P := by
          have heq : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
          rw [heq]; exact hy
        exact (hg_iff (g⁻¹ * y * g)).mpr hmem
      · change g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [← thompsonJ_map_of_injective hinj P p, hP_conj]

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

/-- A normal `p`-complement descends along an inclusion of finite subgroups. -/
theorem hasNormalPComplement_of_le
    [Finite G] {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hBA : B ≤ A)
    (hA : OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥A) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥B := by
  have hSub := OddOrder.Isaacs.Ch05.hasNormalPComplement_of_subgroup hA
    (B.subgroupOf A)
  exact hasNormalPComplement_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hBA) hSub

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

section MinimalCounterexampleStepOne

/-- The normalizer of a subgroup also normalizes its Thompson subgroup. -/
theorem normalizer_le_normalizer_thompsonJ
    [Finite G] {p : ℕ} (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((Subgroup.thompsonJ S p : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hconj :
      (Subgroup.thompsonJ S p).map (MulAut.conj g).toMonoidHom =
        Subgroup.thompsonJ S p :=
    Subgroup.thompsonJ_map_conj_eq_of_mem_normalizer hg
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈
        (Subgroup.thompsonJ S p).map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, rfl⟩
    rwa [hconj] at hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈
        (Subgroup.thompsonJ S p).map (MulAut.conj g).toMonoidHom := by
      rw [hconj]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have hxy : x = y := by
      have : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      exact (mul_left_cancel (mul_right_cancel this)).symm
    rwa [hxy]

/-- `normalizerPPart` is the order of every Sylow `p`-subgroup of the
normalizer. -/
theorem normalizerPPart_eq_card_sylow
    [Finite G] {p : ℕ} [Fact p.Prime] (U : Subgroup G)
    (S : Sylow p ↥(Subgroup.normalizer (U : Set G))) :
    normalizerPPart p U =
      Nat.card (S : Subgroup ↥(Subgroup.normalizer (U : Set G))) := by
  rw [normalizerPPart, S.card_eq_multiplicity]

/-- Every `p`-subgroup of `N_G(U)` has order at most `normalizerPPart p U`. -/
theorem card_le_normalizerPPart_of_isPGroup
    [Finite G] {p : ℕ} [Fact p.Prime] (U : Subgroup G)
    {R : Subgroup ↥(Subgroup.normalizer (U : Set G))} (hR : IsPGroup p R) :
    Nat.card R ≤ normalizerPPart p U := by
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  rw [normalizerPPart_eq_card_sylow U S]
  exact Subgroup.card_le_of_le hRS

end MinimalCounterexampleStepOne

section MinimalCounterexampleStepTwo

/-- If one Sylow `p`-subgroup is trivial, the whole group is its own normal
`p`-complement. -/
theorem hasNormalPComplement_of_sylow_eq_bot
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : (P : Subgroup G) = ⊥) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  refine ⟨⊤, inferInstance, fun Q => ?_⟩
  have hQP : (Q : Subgroup G) = (P : Subgroup G) :=
    P.is_maximal' Q.isPGroup' (by rw [hP]; exact bot_le)
  rw [hQP, hP]
  exact Subgroup.isComplement'_top_bot

/-- The correspondence theorem identifies normalizers after quotienting by a
normal subgroup contained in the subgroup being normalized. -/
theorem normalizer_map_quotient_eq_of_le
    [Finite G] {N : Subgroup G} [N.Normal] {X : Subgroup G} (hNX : N ≤ X) :
    Subgroup.normalizer
        ((X.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
      (Subgroup.normalizer (X : Set G)).map (QuotientGroup.mk' N) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hker : q.ker = N := QuotientGroup.ker_mk' N
  have hker_le_X : q.ker ≤ X := by simpa only [hker] using hNX
  apply Subgroup.comap_injective hq
  rw [Subgroup.comap_normalizer_eq_of_surjective _ hq]
  rw [Subgroup.comap_map_eq_self hker_le_X]
  rw [Subgroup.comap_map_eq_self (hker_le_X.trans Subgroup.le_normalizer)]

/-- For the lexicographically maximal bad subgroup `U`, every strictly larger
`p`-subgroup `X` lying in a Sylow subgroup and normalized by that Sylow subgroup
has a normalizer with a normal `p`-complement. -/
theorem hasNormalPComplement_normalizer_of_maximal_bad_lt
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {U X : Subgroup G} [U.Normal]
    (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ Y : Subgroup G, IsBadNormalizerPSubgroup p Y →
      normalizerPPart p Y ≤ normalizerPPart p U)
    (hU_card_max : ∀ Y : Subgroup G, IsBadNormalizerPSubgroup p Y →
      normalizerPPart p Y = normalizerPPart p U → Nat.card Y ≤ Nat.card U)
    (hUX : U < X) (hXP : X ≤ (P : Subgroup G))
    (hP_normalizes_X : (P : Subgroup G) ≤ Subgroup.normalizer (X : Set G)) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer (X : Set G)) := by
  by_contra hNX
  have hX_ne : X ≠ ⊥ := by
    intro hX
    apply hU_bad.1
    exact le_bot_iff.mp (hUX.le.trans (le_of_eq hX))
  have hX_p : IsPGroup p X := P.isPGroup'.to_le hXP
  have hX_bad : IsBadNormalizerPSubgroup p X := ⟨hX_ne, hX_p, hNX⟩
  have hNU_top : Subgroup.normalizer (U : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have htop_card : Nat.card ↥(⊤ : Subgroup G) = Nat.card G :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  have hU_weight : normalizerPPart p U = Nat.card (P : Subgroup G) := by
    rw [normalizerPPart, hNU_top, htop_card, P.card_eq_multiplicity]
  have hP_sub_p :
      IsPGroup p
        ((P : Subgroup G).subgroupOf (Subgroup.normalizer (X : Set G))) :=
    P.isPGroup'.comap_subtype
  have hP_card_le : Nat.card (P : Subgroup G) ≤ normalizerPPart p X := by
    calc
      Nat.card (P : Subgroup G) =
          Nat.card
            ((P : Subgroup G).subgroupOf (Subgroup.normalizer (X : Set G))) :=
        (Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hP_normalizes_X).toEquiv).symm
      _ ≤ normalizerPPart p X :=
        card_le_normalizerPPart_of_isPGroup X hP_sub_p
  have hweight_ge : normalizerPPart p U ≤ normalizerPPart p X :=
    hU_weight.le.trans hP_card_le
  have hweight_le : normalizerPPart p X ≤ normalizerPPart p U :=
    hU_weight_max X hX_bad
  have hweights : normalizerPPart p X = normalizerPPart p U :=
    le_antisymm hweight_le hweight_ge
  have hX_card_le : Nat.card X ≤ Nat.card U :=
    hU_card_max X hX_bad hweights
  have hU_card_lt : Nat.card U < Nat.card X :=
    Set.Finite.card_lt_card (Set.toFinite _)
      (SetLike.coe_ssubset_coe.mpr hUX)
  exact (not_lt_of_ge hX_card_le) hU_card_lt

/-- **Isaacs Theorem 7.1, Step 2.**

Let `U` be the lexicographically maximal bad `p`-subgroup, already known to
be normal.  Then `G/U` has a normal `p`-complement.  For a Sylow subgroup
`P` containing `U`, every nontrivial subgroup of `P/U` used in the Thompson
local hypotheses has inverse image strictly above `U`; maximality therefore
gives a normal `p`-complement in its upstairs normalizer.  The correspondence
theorem transports this complement back to the quotient normalizer, and the
minimal-order hypothesis applies to `G/U`. -/
theorem _root_.solution.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    {U : Subgroup G} [U.Normal]
    (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X ≤ normalizerPPart p U)
    (hU_card_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X = normalizerPPart p U → Nat.card X ≤ Nat.card U) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p (G ⧸ U) := by
  classical
  obtain ⟨P, hUP⟩ := hU_bad.2.1.exists_le_sylow
  let q : G →* G ⧸ U := QuotientGroup.mk' U
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective U
  have hker : q.ker = U := QuotientGroup.ker_mk' U
  set Pbar : Sylow p (G ⧸ U) := P.mapSurjective hq with hPbar_def
  have hPbar_coe :
      (Pbar : Subgroup (G ⧸ U)) = (P : Subgroup G).map q := by
    rw [hPbar_def, Sylow.coe_mapSurjective]
  by_cases hPbar_bot : (Pbar : Subgroup (G ⧸ U)) = ⊥
  · exact hasNormalPComplement_of_sylow_eq_bot Pbar hPbar_bot
  have hPbar_comap :
      (Pbar : Subgroup (G ⧸ U)).comap q = (P : Subgroup G) := by
    rw [hPbar_coe]
    exact Subgroup.comap_map_eq_self (by simpa only [hker] using hUP)
  have quotientNormalizer_hasNormalPComplement
      (Xbar : Subgroup (G ⧸ U)) (hXbar_ne : Xbar ≠ ⊥)
      (hXbar_le : Xbar ≤ (Pbar : Subgroup (G ⧸ U)))
      (hPbar_normalizes_Xbar :
        (Pbar : Subgroup (G ⧸ U)) ≤
          Subgroup.normalizer (Xbar : Set (G ⧸ U))) :
      OddOrder.Isaacs.Ch05.HasNormalPComplement p
        ↥(Subgroup.normalizer (Xbar : Set (G ⧸ U))) := by
    set X : Subgroup G := Xbar.comap q with hX_def
    have hUX : U < X := by
      have hcomap_lt :
          (⊥ : Subgroup (G ⧸ U)).comap q < Xbar.comap q :=
        (Subgroup.comap_lt_comap_of_surjective hq).2
          (bot_lt_iff_ne_bot.mpr hXbar_ne)
      simpa only [MonoidHom.comap_bot, hker, hX_def] using hcomap_lt
    have hXP : X ≤ (P : Subgroup G) := by
      rw [hX_def, ← hPbar_comap]
      exact Subgroup.comap_mono hXbar_le
    have hP_normalizes_X :
        (P : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
      have hcomap :
          (Pbar : Subgroup (G ⧸ U)).comap q ≤
            (Subgroup.normalizer (Xbar : Set (G ⧸ U))).comap q :=
        Subgroup.comap_mono hPbar_normalizes_Xbar
      rw [Subgroup.comap_normalizer_eq_of_surjective _ hq, hPbar_comap] at hcomap
      simpa only [hX_def] using hcomap
    have hNX :=
      hasNormalPComplement_normalizer_of_maximal_bad_lt P hU_bad
        hU_weight_max hU_card_max hUX hXP hP_normalizes_X
    have hImage :=
      hasNormalPComplement_subgroup_map q
        (Subgroup.normalizer (X : Set G)) hNX
    have hX_map : X.map q = Xbar := by
      rw [hX_def]
      exact Subgroup.map_comap_eq_self_of_surjective hq Xbar
    have hNormalizer_image :
        Subgroup.normalizer (Xbar : Set (G ⧸ U)) =
          (Subgroup.normalizer (X : Set G)).map q := by
      rw [← hX_map]
      exact normalizer_map_quotient_eq_of_le hUX.le
    exact hasNormalPComplement_of_mulEquiv
      (MulEquiv.subgroupCongr hNormalizer_image.symm) hImage
  have hcard : Nat.card (G ⧸ U) < Nat.card G :=
    Subgroup.card_quotient_lt_of_ne_bot hU_bad.1
  refine ih (G ⧸ U) hcard ?_
  rw [hasThompsonPComplementHypothesis_iff Pbar]
  set Zbar : Subgroup (G ⧸ U) :=
    (Subgroup.center ↥(Pbar : Subgroup (G ⧸ U))).map
      (Pbar : Subgroup (G ⧸ U)).subtype with hZbar_def
  set Jbar : Subgroup (G ⧸ U) :=
    Subgroup.thompsonJ (Pbar : Subgroup (G ⧸ U)) p with hJbar_def
  have : Nontrivial ↥(Pbar : Subgroup (G ⧸ U)) :=
    (Pbar : Subgroup (G ⧸ U)).nontrivial_iff_ne_bot.mpr hPbar_bot
  have hZbar_ne : Zbar ≠ ⊥ := by
    rw [hZbar_def, Ne,
      Subgroup.map_eq_bot_iff_of_injective _
        (Pbar : Subgroup (G ⧸ U)).subtype_injective]
    exact (Subgroup.center ↥(Pbar : Subgroup (G ⧸ U))).nontrivial_iff_ne_bot.mp
      Pbar.isPGroup'.center_nontrivial
  have hZbar_le : Zbar ≤ (Pbar : Subgroup (G ⧸ U)) := by
    rw [hZbar_def]
    exact Subgroup.map_subtype_le _
  have hPbar_normalizes_Zbar :
      (Pbar : Subgroup (G ⧸ U)) ≤
        Subgroup.normalizer (Zbar : Set (G ⧸ U)) := by
    intro g hg
    rw [hZbar_def]
    exact Subgroup.mem_normalizer_center_map_of_mem_normalizer
      (Subgroup.le_normalizer hg)
  have hNZbar := quotientNormalizer_hasNormalPComplement Zbar hZbar_ne
    hZbar_le hPbar_normalizes_Zbar
  have hCZbar :
      OddOrder.Isaacs.Ch05.HasNormalPComplement p
        ↥(Subgroup.centralizer (Zbar : Set (G ⧸ U))) :=
    hasNormalPComplement_of_le
      (Subgroup.centralizer_le_normalizer (Zbar : Set (G ⧸ U))) hNZbar
  have hJbar_ne : Jbar ≠ ⊥ := by
    rw [hJbar_def]
    exact Subgroup.thompsonJ_ne_bot Pbar.isPGroup' hPbar_bot
  have hJbar_le : Jbar ≤ (Pbar : Subgroup (G ⧸ U)) := by
    rw [hJbar_def]
    exact Subgroup.thompsonJ_le _ _
  have hPbar_normalizes_Jbar :
      (Pbar : Subgroup (G ⧸ U)) ≤
        Subgroup.normalizer (Jbar : Set (G ⧸ U)) := by
    rw [hJbar_def]
    exact Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_thompsonJ (Pbar : Subgroup (G ⧸ U)))
  have hNJbar := quotientNormalizer_hasNormalPComplement Jbar hJbar_ne
    hJbar_le hPbar_normalizes_Jbar
  simpa only [HasThompsonLocalPComplements, hZbar_def, hJbar_def] using
    And.intro hCZbar hNJbar

end MinimalCounterexampleStepTwo

end OddOrder.Isaacs.Ch07
