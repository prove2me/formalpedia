-- Prove2me | solution 1 for UnderstandingML.compression_realizable_to_agnostic
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T05:11:37.73372+00:00
-- url     : https://prove2.me/submissions/f13c4817-cfc6-4c49-a570-508977075d5a

import Definitions.Def_UnderstandingML_Compression

open MeasureTheory
open scoped InnerProductSpace

open UnderstandingML in
theorem solution {X : Type*} (H : Set (X → Bool)) (k : ℕ)
    (hH : HasCompressionScheme H k) : HasAgnosticCompressionScheme H k := by
  classical
  intro m hm
  obtain ⟨sel, B, hBH, hcorr⟩ := hH m hm
  -- pointwise domination of the loss gives domination of the empirical risk
  have emp_le : ∀ (S : Fin m → X × Bool) (g h : X → Bool),
      (∀ i, lossMulti g (S i) ≤ lossMulti h (S i)) →
        empRisk lossMulti S g ≤ empRisk lossMulti S h := by
    intro S g h hgh
    unfold empRisk
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ ↦ hgh i) (Nat.cast_nonneg _)
  have loss_le_one : ∀ (g : X → Bool) (z : X × Bool), lossMulti g z ≤ 1 := by
    intro g z; unfold lossMulti; split_ifs <;> norm_num
  have key : ∀ S : Fin m → X × Bool, ∃ t : Fin k → Fin m,
      ∀ h ∈ H, empRisk lossMulti S (B (fun j ↦ S (t j))) ≤ empRisk lossMulti S h := by
    intro S
    by_cases hne : H.Nonempty
    swap
    · exact ⟨fun _ ↦ ⟨0, hm⟩, fun h hh ↦ (hne ⟨h, hh⟩).elim⟩
    -- an ERM hypothesis exists, since the empirical risk takes finitely many values
    obtain ⟨hstar, hstarH, hERM⟩ : ∃ hstar ∈ H,
        ∀ h ∈ H, empRisk lossMulti S hstar ≤ empRisk lossMulti S h := by
      set T := (fun h ↦ empRisk lossMulti S h) '' H with hT
      have hTfin : T.Finite := by
        refine (Set.finite_range (fun v : Fin m → Bool ↦
          (∑ i, (if v i = (S i).2 then (0 : ℝ) else 1)) / (m : ℝ))).subset ?_
        rintro _ ⟨h, _, rfl⟩
        exact ⟨fun i ↦ h (S i).1, by simp only [empRisk, lossMulti]; congr 1; exact Finset.sum_congr rfl fun i _ ↦ by congr⟩
      obtain ⟨r, ⟨h0, h0H, rfl⟩, hmin⟩ :=
        Set.exists_min_image T id hTfin (hne.image _)
      exact ⟨h0, h0H, fun h hh ↦ hmin _ ⟨h, hh, rfl⟩⟩
    -- it suffices to dominate `hstar` pointwise
    suffices ∃ t : Fin k → Fin m,
        ∀ i, lossMulti (B (fun j ↦ S (t j))) (S i) ≤ lossMulti hstar (S i) by
      obtain ⟨t, ht⟩ := this
      exact ⟨t, fun h hh ↦ (emp_le S _ _ ht).trans (hERM h hh)⟩
    by_cases hc : ∃ i0, hstar (S i0).1 = (S i0).2
    · obtain ⟨i0, hi0⟩ := hc
      -- redirect every position to a position where `hstar` is correct
      let σ : Fin m → Fin m := fun i ↦ if hstar (S i).1 = (S i).2 then i else i0
      have hσ : ∀ i, hstar (S (σ i)).1 = (S (σ i)).2 := by
        intro i; simp only [σ]; split_ifs with h <;> assumption
      let x' : Fin m → X := fun i ↦ (S (σ i)).1
      have hS'' : (fun i ↦ (x' i, hstar (x' i))) = fun i ↦ S (σ i) := by
        funext i; simp only [x', hσ i]
      refine ⟨fun j ↦ σ (sel (fun i ↦ (x' i, hstar (x' i))) j), fun i ↦ ?_⟩
      by_cases hi : hstar (S i).1 = (S i).2
      · have hσi : σ i = i := by simp [σ, hi]
        have := hcorr hstar hstarH x' i
        unfold compressedHyp at this
        have hx : x' i = (S i).1 := by simp [x', hσi]
        rw [hx] at this
        have hB : B (fun j ↦ S (σ (sel (fun i ↦ (x' i, hstar (x' i))) j))) (S i).1 =
            (S i).2 := by
          rw [← hi, ← this]
          congr 2
          funext j
          exact congrFun hS''.symm _
        simp [lossMulti, hB, hi]
      · have : lossMulti hstar (S i) = 1 := by simp [lossMulti, hi]
        rw [this]; exact loss_le_one _ _
    · push_neg at hc
      refine ⟨fun _ ↦ ⟨0, hm⟩, fun i ↦ ?_⟩
      have : lossMulti hstar (S i) = 1 := by simp [lossMulti, hc i]
      rw [this]; exact loss_le_one _ _
  choose t ht using key
  exact ⟨t, B, hBH, fun S h hh ↦ ht S h hh⟩
