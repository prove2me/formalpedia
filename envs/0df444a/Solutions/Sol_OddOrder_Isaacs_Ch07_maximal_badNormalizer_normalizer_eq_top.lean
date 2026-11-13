-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.maximal_badNormalizer_normalizer_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T06:00:03.256857+00:00
-- url     : https://prove2.me/submissions/a8d91bc8-d7f4-4b3b-a309-1588b980dfaa

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Mathlib/Subgroup.lean
--   OddOrder/GroupTheory/ThompsonSubgroup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
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
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Theorems.Thm_Subgroup_thompsonJ_ne_bot
import Theorems.Thm_OddOrder_Isaacs_Ch07_hasNormalPComplement_of_mulEquiv
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

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section LocalHypothesisTransport

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

/-- Failure of a Thompson local hypothesis produces a nontrivial bad
`p`-subgroup, either the ambient center of `S` or its Thompson subgroup.  Every
subgroup normalizing `S` also normalizes the selected subgroup. -/
theorem exists_badNormalizerPSubgroup_of_not_hasThompsonLocalPComplements
    [Finite G] {p : ℕ} [Fact p.Prime] {S T : Subgroup G}
    (hS_p : IsPGroup p S) (hS_ne : S ≠ ⊥)
    (hT_norm : T ≤ Subgroup.normalizer (S : Set G))
    (hLocal : ¬ HasThompsonLocalPComplements p S) :
    ∃ X : Subgroup G,
      IsBadNormalizerPSubgroup p X ∧
        T ≤ Subgroup.normalizer (X : Set G) := by
  classical
  rw [HasThompsonLocalPComplements] at hLocal
  rcases not_and_or.mp hLocal with hCenter | hJ
  · set Z : Subgroup G := (Subgroup.center ↥S).map S.subtype with hZ_def
    have hZ_ne : Z ≠ ⊥ := by
      rw [hZ_def, Ne, Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective]
      have : Nontrivial ↥S := S.nontrivial_iff_ne_bot.mpr hS_ne
      exact (Subgroup.center ↥S).nontrivial_iff_ne_bot.mp hS_p.center_nontrivial
    have hZ_p : IsPGroup p Z := by
      rw [hZ_def]
      exact (hS_p.to_subgroup (Subgroup.center ↥S)).map S.subtype
    have hNZ :
        ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p
          ↥(Subgroup.normalizer (Z : Set G)) := by
      intro h
      exact hCenter
        (hasNormalPComplement_of_le
          (Subgroup.centralizer_le_normalizer (Z : Set G)) h)
    refine ⟨Z, ⟨hZ_ne, hZ_p, hNZ⟩, ?_⟩
    intro t ht
    exact Subgroup.mem_normalizer_center_map_of_mem_normalizer (hT_norm ht)
  · set J : Subgroup G := Subgroup.thompsonJ S p with hJ_def
    have hJ_ne : J ≠ ⊥ := by
      rw [hJ_def]
      exact Subgroup.thompsonJ_ne_bot hS_p hS_ne
    have hJ_p : IsPGroup p J := by
      rw [hJ_def]
      exact hS_p.of_injective
        (Subgroup.inclusion (Subgroup.thompsonJ_le S p))
        (Subgroup.inclusion_injective _)
    refine ⟨J, ⟨hJ_ne, hJ_p, hJ⟩, ?_⟩
    exact hT_norm.trans (normalizer_le_normalizer_thompsonJ S)

/-- **§7C/§7D helper** — normalizer-grows. If `D < ↑S` for a finite
`p`-group Sylow `S`, then `D` is strictly contained in `N_H(D) ⊓ ↑S`. -/
theorem lt_normalizer_inf_sylow_of_lt
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (S : Sylow p H) {D : Subgroup H} (hD_lt : D < (S : Subgroup H)) :
    D < Subgroup.normalizer D ⊓ (S : Subgroup H) := by
  classical
  have : Group.IsNilpotent ↥(S : Subgroup H) := S.isPGroup'.isNilpotent
  have hNC : NormalizerCondition ↥(S : Subgroup H) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup H))
  have hD_le : D ≤ (S : Subgroup H) := le_of_lt hD_lt
  have hsub_lt_top : D.subgroupOf (S : Subgroup H) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact (ne_of_lt hD_lt) (le_antisymm hD_le htop)
  have hlt := hNC (D.subgroupOf (S : Subgroup H)) hsub_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hD_le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hD_le) ?_
  intro heq
  apply ht_not
  have : (t : H) ∈ Subgroup.normalizer D ⊓ (S : Subgroup H) := ⟨ht_norm, t.2⟩
  rw [← heq] at this
  exact this

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

/-- **Isaacs Theorem 7.1, Step 1 (normalizer growth).**

The first, `normalizerPPart`, maximality condition forces the selected bad
`p`-subgroup to be normal.  If its normalizer were proper, induction would
produce a failed Thompson local hypothesis there.  A larger ambient
`p`-subgroup normalizing the corresponding center or Thompson subgroup would
then give a bad subgroup with strictly larger normalizer `p`-part. -/
theorem _root_.solution.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    {U : Subgroup G} (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X ≤ normalizerPPart p U) :
    Subgroup.normalizer (U : Set G) = ⊤ := by
  classical
  set N : Subgroup G := Subgroup.normalizer (U : Set G) with hN_def
  change N = ⊤
  by_contra hN_ne_top
  have hN_card : Nat.card N < Nat.card G :=
    Subgroup.card_lt_card_of_ne_top hN_ne_top
  have hN_no_complement :
      ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p N := by
    simpa only [hN_def] using hU_bad.2.2
  have hN_not_hyp : ¬ HasThompsonPComplementHypothesis p N := by
    intro hN_hyp
    exact hN_no_complement (ih N hN_card hN_hyp)
  rw [HasThompsonPComplementHypothesis] at hN_not_hyp
  push Not at hN_not_hyp
  obtain ⟨S, hS_local_fail⟩ := hN_not_hyp
  have hU_le_N : U ≤ N := by
    rw [hN_def]
    exact Subgroup.le_normalizer
  have hUN_p : IsPGroup p (U.subgroupOf N) := hU_bad.2.1.comap_subtype
  have hUN_normal : (U.subgroupOf N).Normal := by
    rw [hN_def]
    exact Subgroup.normal_in_normalizer
  have hUN_le_S : U.subgroupOf N ≤ (S : Subgroup N) :=
    (OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hUN_p).trans
      (OddOrder.Isaacs.Ch01.opCore_le S)
  have hUN_ne : U.subgroupOf N ≠ ⊥ := by
    intro hUN_bot
    apply hU_bad.1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxUN : (⟨x, hU_le_N hx⟩ : N) ∈ U.subgroupOf N := hx
    rw [hUN_bot, Subgroup.mem_bot] at hxUN
    exact congrArg Subtype.val hxUN
  have hS_ne : (S : Subgroup N) ≠ ⊥ := by
    intro hS_bot
    apply hUN_ne
    apply le_antisymm
    · simpa only [hS_bot] using hUN_le_S
    · exact bot_le
  set SH : Subgroup G := (S : Subgroup N).map N.subtype with hSH_def
  have hSH_p : IsPGroup p SH := by
    rw [hSH_def]
    exact S.isPGroup'.map N.subtype
  have hSH_ne : SH ≠ ⊥ := by
    rw [hSH_def, Ne,
      Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective]
    exact hS_ne
  have hSH_local_fail : ¬ HasThompsonLocalPComplements p SH := by
    intro hSH_local
    apply hS_local_fail
    apply HasThompsonLocalPComplements.of_subgroup (G := G) N
    simpa only [hSH_def] using hSH_local
  obtain ⟨P, hSH_le_P⟩ := hSH_p.exists_le_sylow
  have hSH_lt_P : SH < (P : Subgroup G) :=
    lt_of_le_of_ne hSH_le_P (by
      intro hSH_eq_P
      apply hSH_local_fail
      rw [hSH_eq_P]
      exact hHyp P)
  set T : Subgroup G :=
    Subgroup.normalizer (SH : Set G) ⊓ (P : Subgroup G) with hT_def
  have hSH_lt_T : SH < T := by
    rw [hT_def]
    exact lt_normalizer_inf_sylow_of_lt P hSH_lt_P
  have hT_p : IsPGroup p T := by
    rw [hT_def]
    exact P.isPGroup'.to_le inf_le_right
  have hT_normalizes_SH : T ≤ Subgroup.normalizer (SH : Set G) := by
    rw [hT_def]
    exact inf_le_left
  obtain ⟨X, hX_bad, hT_normalizes_X⟩ :=
    exists_badNormalizerPSubgroup_of_not_hasThompsonLocalPComplements
      hSH_p hSH_ne hT_normalizes_SH hSH_local_fail
  have hT_sub_p :
      IsPGroup p (T.subgroupOf (Subgroup.normalizer (X : Set G))) :=
    hT_p.comap_subtype
  have hT_le_weight : Nat.card T ≤ normalizerPPart p X := by
    calc
      Nat.card T =
          Nat.card (T.subgroupOf (Subgroup.normalizer (X : Set G))) :=
        (Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hT_normalizes_X).toEquiv).symm
      _ ≤ normalizerPPart p X :=
        card_le_normalizerPPart_of_isPGroup X hT_sub_p
  have hSH_card_lt_T : Nat.card SH < Nat.card T := by
    exact Set.Finite.card_lt_card (Set.toFinite _)
      (SetLike.coe_ssubset_coe.mpr hSH_lt_T)
  have hSH_card : Nat.card SH = Nat.card (S : Subgroup N) := by
    rw [hSH_def, Subgroup.card_map_of_injective N.subtype_injective]
  have hU_weight :
      normalizerPPart p U = Nat.card (S : Subgroup N) := by
    simpa only [hN_def] using normalizerPPart_eq_card_sylow U S
  have hweight_lt : normalizerPPart p U < normalizerPPart p X := by
    calc
      normalizerPPart p U = Nat.card (S : Subgroup N) := hU_weight
      _ = Nat.card SH := hSH_card.symm
      _ < Nat.card T := hSH_card_lt_T
      _ ≤ normalizerPPart p X := hT_le_weight
  exact (not_lt_of_ge (hU_weight_max X hX_bad)) hweight_lt

end MinimalCounterexampleStepOne

end OddOrder.Isaacs.Ch07
