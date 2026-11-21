-- Prove2me | solution 1 for RandOnlineSetCoverSqrt.LowerBound.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:42:52.403048+00:00
-- url     : https://prove2.me/submissions/6de7433f-b458-4262-8056-8db11cc4e517

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates

section
namespace RandOnlineSetCoverSqrt.Dev.L31
open RandOnlineSetCoverSqrt.LowerBound

theorem card_le (m r : ℕ) :
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => S.card ≤ r)).card ≤ batchBound m r := by
  have : (Finset.univ : Finset (Finset (Fin m))).filter (fun S => S.card ≤ r) =
      (Finset.range (r+1)).biUnion (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin m))) := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [this]
  refine (Finset.card_biUnion_le).trans ?_
  unfold batchBound
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro j _
  simp [Finset.card_powersetCard]

end RandOnlineSetCoverSqrt.Dev.L31

namespace RandOnlineSetCoverSqrt.LowerBound
open RandOnlineSetCoverSqrt.Dev.L31

theorem chk_lemma_3_1 {m : ℕ} (D : Family m) (hD : D.Nonempty)
    (hne : ∀ W ∈ D, W.Nonempty) (r : ℕ) (hr : 1 ≤ r) :
    ∃ B : List (Element m), Forcing r D B ∧ B.length ≤ batchBound m r := by
  classical
  refine ⟨forcingBatch r D, ?_, ?_⟩
  · intro X hX
    have mem : ∀ u : Element m, u ∈ forcingBatch r D ↔
        ((Finset.univ \ u.val).card ≤ r ∧ ∀ W ∈ D, (u.val ∩ W).Nonempty) := by
      intro u; unfold forcingBatch; simp
    unfold CoversBatch RandOnlineSetCover.InfoLB.Covers incidences
    constructor
    · intro h
      by_contra hno
      have hno : ∀ W ∈ D, ¬ W ⊆ X := fun W hW hs => hno ⟨W, hW, hs⟩
      have hXu : X ≠ Finset.univ := by
        intro hX'
        obtain ⟨W, hW⟩ := hD
        exact hno W hW (hX' ▸ Finset.subset_univ _)
      have hne' : (Xᶜ).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h0
        apply hXu; rw [Finset.compl_eq_empty_iff] at h0; exact h0
      have hmem : (⟨Xᶜ, hne'⟩ : Element m) ∈ forcingBatch r D := by
        rw [mem]
        refine ⟨?_, ?_⟩
        · simpa [Finset.compl_eq_univ_sdiff] using hX
        · intro W hW
          obtain ⟨x, hxW, hxX⟩ := Finset.not_subset.mp (hno W hW)
          exact ⟨x, by simp [hxW, hxX]⟩
      obtain ⟨x, hx⟩ := h Xᶜ (List.mem_map.mpr ⟨_, hmem, rfl⟩)
      simp at hx
    · rintro ⟨W, hW, hWX⟩ e he
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
      obtain ⟨x, hx⟩ := ((mem u).mp hu).2 W hW
      exact ⟨x, by simp at hx ⊢; exact ⟨hWX hx.2, hx.1⟩⟩
  · unfold forcingBatch
    rw [Finset.length_toList]
    refine le_trans ?_ (card_le m r)
    refine Finset.card_le_card_of_injOn (fun u => Finset.univ \ u.val) ?_ ?_
    · intro u hu
      simp at hu ⊢; exact hu.1
    · intro u _ v _ h
      apply Subtype.ext
      have := congrArg (fun S => Finset.univ \ S) h
      simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using this

end RandOnlineSetCoverSqrt.LowerBound
end

theorem solution : type_of% @RandOnlineSetCoverSqrt.LowerBound.chk_lemma_3_1 := @RandOnlineSetCoverSqrt.LowerBound.chk_lemma_3_1
