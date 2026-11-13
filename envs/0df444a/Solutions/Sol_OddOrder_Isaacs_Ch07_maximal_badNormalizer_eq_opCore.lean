-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.maximal_badNormalizer_eq_opCore
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T06:02:52.877252+00:00
-- url     : https://prove2.me/submissions/a4522a41-f37e-4bd5-90e7-2f253e61e9da

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
import Theorems.Thm_OddOrder_Isaacs_Ch07_maximal_badNormalizer_normalizer_eq_top

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepOne

/-- **Isaacs Theorem 7.1, Step 1.**

The lexicographically maximal bad `p`-subgroup is `O_p(G)`.  The first
maximality coordinate makes it normal; maximality of its order among equal
normalizer `p`-parts then identifies it with the largest normal `p`-subgroup. -/
theorem _root_.solution.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    {U : Subgroup G} (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X ≤ normalizerPPart p U)
    (hU_card_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X = normalizerPPart p U → Nat.card X ≤ Nat.card U) :
    U = OddOrder.Isaacs.Ch01.opCore p G := by
  have hNU_top :=
    maximal_badNormalizer_normalizer_eq_top hHyp ih hU_bad hU_weight_max
  have hU_normal : U.Normal := Subgroup.normalizer_eq_top_iff.mp hNU_top
  set O : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hO_def
  have hU_le_O : U ≤ O := by
    rw [hO_def]
    exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hU_bad.2.1
  have hO_ne : O ≠ ⊥ := by
    intro hO_bot
    apply hU_bad.1
    exact le_bot_iff.mp (hU_le_O.trans (le_of_eq hO_bot))
  have hO_p : IsPGroup p O := by
    rw [hO_def]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hNO_top : Subgroup.normalizer (O : Set G) = ⊤ := by
    apply Subgroup.normalizer_eq_top_iff.mpr
    rw [hO_def]
    exact OddOrder.Isaacs.Ch01.opCore.normal p G
  have hnormalizers :
      Subgroup.normalizer (O : Set G) = Subgroup.normalizer (U : Set G) :=
    hNO_top.trans hNU_top.symm
  have hO_no_complement :
      ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p
        ↥(Subgroup.normalizer (O : Set G)) := by
    rw [hnormalizers]
    exact hU_bad.2.2
  have hO_bad : IsBadNormalizerPSubgroup p O :=
    ⟨hO_ne, hO_p, hO_no_complement⟩
  have hweights : normalizerPPart p O = normalizerPPart p U := by
    rw [normalizerPPart, normalizerPPart, hnormalizers]
  have hO_card_le : Nat.card O ≤ Nat.card U :=
    hU_card_max O hO_bad hweights
  have hU_eq_O : U = O :=
    Subgroup.eq_of_le_of_card_ge hU_le_O hO_card_le
  simpa only [hO_def] using hU_eq_O

end MinimalCounterexampleStepOne

end OddOrder.Isaacs.Ch07
