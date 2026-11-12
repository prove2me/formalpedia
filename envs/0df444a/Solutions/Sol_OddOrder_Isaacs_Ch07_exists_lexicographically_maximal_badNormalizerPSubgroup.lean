-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.exists_lexicographically_maximal_badNormalizerPSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:42.550064+00:00
-- url     : https://prove2.me/submissions/5e372be6-e695-4436-be84-44d4f8f20316

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
import Theorems.Thm_OddOrder_Isaacs_Ch05_hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer
import Theorems.Thm_OddOrder_Isaacs_Ch05_isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepOne

/-- **Isaacs Theorem 7.1, Step 1 (bad subgroup existence).**

If `G` has no normal `p`-complement, Frobenius' normal-complement criterion
forces some nontrivial `p`-subgroup to have a normalizer without one. -/
theorem exists_isBadNormalizerPSubgroup
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G) :
    ∃ U : Subgroup G, IsBadNormalizerPSubgroup p U := by
  by_contra hbad
  apply hG
  rw [OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer]
  intro X hXp
  exact
    OddOrder.Isaacs.Ch05.isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
      (fun Y hY_ne hYp => by
        by_contra hNY
        exact hbad ⟨Y, hY_ne, hYp, hNY⟩)
      X hXp

/-- **Isaacs Theorem 7.1, Step 1 (lexicographic choice of `U`).**

Among all bad `p`-subgroups choose `U` first maximizing the `p`-part of
`|N_G(U)|`, then maximizing `|U|` among ties.  The witness is selected from the
finite type of subgroups, so the maximality data are constructed rather than
postulated. -/
theorem _root_.solution
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G) :
    ∃ U : Subgroup G,
      IsBadNormalizerPSubgroup p U ∧
      (∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
        normalizerPPart p X ≤ normalizerPPart p U) ∧
      (∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
        normalizerPPart p X = normalizerPPart p U → Nat.card X ≤ Nat.card U) := by
  classical
  let : Fintype (Subgroup G) := Fintype.ofFinite _
  let family : Finset (Subgroup G) :=
    Finset.univ.filter (IsBadNormalizerPSubgroup p)
  obtain ⟨U₀, hU₀⟩ := exists_isBadNormalizerPSubgroup hG
  have hU₀_mem : U₀ ∈ family :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU₀⟩
  have hfamily : family.Nonempty := ⟨U₀, hU₀_mem⟩
  obtain ⟨V, hV_mem, hV_max⟩ :=
    family.exists_max_image (normalizerPPart p) hfamily
  let tied : Finset (Subgroup G) :=
    family.filter (fun X => normalizerPPart p X = normalizerPPart p V)
  have hV_tied : V ∈ tied :=
    Finset.mem_filter.mpr ⟨hV_mem, rfl⟩
  obtain ⟨U, hU_tied, hU_max⟩ :=
    tied.exists_max_image (fun X => Nat.card X) ⟨V, hV_tied⟩
  obtain ⟨hU_mem, hU_weight⟩ := Finset.mem_filter.mp hU_tied
  have hU_bad : IsBadNormalizerPSubgroup p U :=
    (Finset.mem_filter.mp hU_mem).2
  refine ⟨U, hU_bad, ?_, ?_⟩
  · intro X hX
    have hX_mem : X ∈ family :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩
    exact (hV_max X hX_mem).trans_eq hU_weight.symm
  · intro X hX hX_weight
    have hX_mem : X ∈ family :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩
    have hX_tied : X ∈ tied := by
      apply Finset.mem_filter.mpr
      refine ⟨hX_mem, ?_⟩
      exact hX_weight.trans hU_weight
    exact hU_max X hX_tied

end MinimalCounterexampleStepOne

end OddOrder.Isaacs.Ch07
