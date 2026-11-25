-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SplitRow_IdxV_relIndex_pi__f86b704c6d51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:34.892199+00:00
-- url     : https://prove2.me/submissions/29cbd9e7-403a-4d4e-8c8b-c78a8b179981

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_HasElemDiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.FinHeis GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.SplitRow.IdxV
namespace GlobalTheory.CompanionTheory.SplitRow.IdxV
theorem _root_.solution {ι G : Type} [Fintype ι] [AddCommGroup G] (H K : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ H).relIndex (AddSubgroup.pi Set.univ K) = ∏ i, (H i).relIndex (K i) := by
  let f : (∀ i, K i) →+ (ι → G) :=
    { toFun := fun x i => (x i : G), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h1 : AddSubgroup.pi Set.univ K = (⊤ : AddSubgroup (∀ i, K i)).map f := by
    ext x
    simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_true_left, AddSubgroup.mem_map,
      AddSubgroup.mem_top, true_and]
    exact ⟨fun h => ⟨fun i => ⟨x i, h i⟩, rfl⟩, by rintro ⟨y, rfl⟩ i; exact (y i).2⟩
  rw [h1, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right]
  simp only [AddSubgroup.relIndex]
  simp only [AddSubgroup.index]
  rw [← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight fun x y => ?_).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_apply]
  refine forall_congr' fun i => ?_
  exact ⟨fun h => QuotientAddGroup.leftRel_apply.2 (h trivial), fun h _ =>
    (QuotientAddGroup.leftRel_apply (s := (H i).addSubgroupOf (K i))).1 h⟩
end GlobalTheory.CompanionTheory.SplitRow.IdxV
