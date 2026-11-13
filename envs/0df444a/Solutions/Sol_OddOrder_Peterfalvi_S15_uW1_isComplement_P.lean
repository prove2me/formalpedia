-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.uW1_isComplement_P
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:17:12.397203+00:00
-- url     : https://prove2.me/submissions/5660b282-f775-4eda-b074-788895a2aa28

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacterBasic

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`U ⋊ W₁` complements `P` in `S`** (structural bridge for (13.18.b), `S`-side form).  From the
`Sdata` complements `M' ⋊ W₁ = S` and `P ⋊ U = M'`, the subgroup `U ⊔ W₁` intersects `P = S_F`
trivially and joins with it to `S`.  This is the `↥S`-internal `IsComplement'` behind the Frobenius
quotient `S̄ = S/P ≅ U ⋊ W₁` used to evaluate `‖Ind_{PW₁}^S 1‖²`.  (Re-derived here in the (13.18)
carve-out rather than exposed from `coprime_card_P_card_UW1`, whose derivation it mirrors.) -/
theorem _root_.solution [Finite G] (hyp : Hypothesis (G := G)) :
    Subgroup.IsComplement' ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) (hyp.P.subgroupOf hyp.S) := by
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hU_le_M' : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hUW1_le_S : hyp.U ⊔ hyp.W1 ≤ hyp.S := sup_le (hU_le_M'.trans hM'_le_S) hW1_le_S
  have hdisj : hyp.P ⊓ hyp.U = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.derived_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxH, hxU⟩
    have hxD : x ∈ derivedInG hyp.S := hyp.Sdata.H_le (by rwa [hyp.Sdata.H_eq, ← hyp.P_eq_SF])
    have hmem : (⟨x, hxD⟩ : ↥(derivedInG hyp.S)) ∈
        (hyp.Sdata.H.subgroupOf (derivedInG hyp.S)) ⊓ (hyp.Sdata.U.subgroupOf (derivedInG hyp.S)) :=
      ⟨Subgroup.mem_subgroupOf.mpr (by rwa [hyp.Sdata.H_eq, ← hyp.P_eq_SF]),
        Subgroup.mem_subgroupOf.mpr (hyp.Sdata_U_eq ▸ hxU)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  have hM'W1 : derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW1⟩
    have hxS : x ∈ hyp.S := hM'_le_S hxM'
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((derivedInG hyp.S).subgroupOf hyp.S) ⊓ (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  have hSsup : hyp.P ⊔ (hyp.U ⊔ hyp.W1) = hyp.S := by
    have htop := hyp.Sdata.M_complement.sup_eq_top
    have hmap := congrArg (Subgroup.map hyp.S.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM'_le_S,
      Subgroup.map_subgroupOf_eq_of_le hyp.Sdata.W1_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [hyp.Sdata_W1_eq, hyp.S_deriv_eq_PU] at hmap
    rw [← sup_assoc]; exact hmap
  have hPUW1_disj : hyp.P ⊓ (hyp.U ⊔ hyp.W1) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxP, hxUW1⟩ := Subgroup.mem_inf.mp hx
    have hxUW1' : (x : G) ∈ (↑(hyp.U ⊔ hyp.W1) : Set G) := hxUW1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.U hyp.W1 hyp.W1_normalizes_U] at hxUW1'
    obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_mul.mp hxUW1'
    have hwM' : w ∈ derivedInG hyp.S := by
      have : w = u⁻¹ * x := by rw [← huw]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hU_le_M' (SetLike.mem_coe.mp hu)))
        (hP_le_M' hxP)
    have hw1 : w = 1 := by
      have : w ∈ derivedInG hyp.S ⊓ hyp.W1 := Subgroup.mem_inf.mpr ⟨hwM', SetLike.mem_coe.mp hw⟩
      rwa [hM'W1, Subgroup.mem_bot] at this
    have hxu : x = u := by rw [← huw, hw1, mul_one]
    have hxPU : x ∈ hyp.P ⊓ hyp.U := Subgroup.mem_inf.mpr ⟨hxP, hxu ▸ SetLike.mem_coe.mp hu⟩
    rwa [hdisj, Subgroup.mem_bot] at hxPU
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff, eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hy
    have hyPU : (y : G) ∈ hyp.P ⊓ (hyp.U ⊔ hyp.W1) := ⟨hy.2, hy.1⟩
    rw [hPUW1_disj, Subgroup.mem_bot] at hyPU
    rw [Subgroup.mem_bot]; exact Subtype.ext hyPU
  · have hsup : ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊔ (hyp.P.subgroupOf hyp.S) = ⊤ := by
      rw [sup_comm, ← Subgroup.subgroupOf_sup hP_le_S hUW1_le_S, hSsup, Subgroup.subgroupOf_self]
    rw [← Subgroup.mul_normal, hsup, Subgroup.coe_top]

end OddOrder.Peterfalvi.S15
