-- Prove2me | solution 1 for SturtRobustStop.Structure.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:50:46.762268+00:00
-- url     : https://prove2.me/submissions/fdf7986d-44b4-40cb-a807-ef44689824d7

import Mathlib
import Definitions.Def_SturtRobustStop_Structure_Pruning

namespace SturtRobustStop.Structure.Aux_SRS

open SturtRobustStop.Structure

theorem firstIndex_eq {T : ℕ} (p : Fin T → Prop) (t0 : Fin T) (h0 : p t0)
    (hlt : ∀ t, t < t0 → ¬ p t) : firstIndex p = some t0 := by
  classical
  unfold firstIndex
  have hne : (Finset.univ.filter p).Nonempty := ⟨t0, by simp [h0]⟩
  rw [dif_pos (by convert hne)]
  congr 1
  apply le_antisymm
  · apply Finset.min'_le
    convert (show t0 ∈ Finset.univ.filter p by simp [h0])
  · apply Finset.le_min'
    intro y hy
    have hy' : p y := by
      have := hy
      simp only [Finset.mem_filter] at this
      exact this.2
    by_contra hc
    exact hlt y (lt_of_not_ge hc) hy'

end SturtRobustStop.Structure.Aux_SRS

open SturtRobustStop.Structure SturtRobustStop.Structure.Aux_SRS in
theorem solution {T N d : ℕ} (D : Model T N d) (μ : Policy T (State d))
    (hμ : TerminalFeasible D μ) :
    IsPruned D (assignedPolicy D (canonicalAssignment D μ hμ)) μ := by
  classical
  set σ := canonicalAssignment D μ hμ with hσ
  have hmem : ∀ i, box D i (σ i) ⊆ μ.stop (σ i) := by
    intro i
    have h := Finset.min'_mem (guaranteedTimes D μ i) (guaranteedTimes_nonempty D μ hμ i)
    unfold guaranteedTimes at h
    simp only [Finset.mem_filter] at h
    exact h.2
  have hmin : ∀ i t, t < σ i → ¬ box D i t ⊆ μ.stop t := by
    intro i t ht hsub
    have h1 : t ∈ guaranteedTimes D μ i := by
      unfold guaranteedTimes
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsub
    have h2 := Finset.min'_le (guaranteedTimes D μ i) t h1
    exact absurd h2 (not_le.mpr ht)
  have hincl : ∀ t, (assignedPolicy D σ).stop t ⊆ μ.stop t := by
    intro t z hz
    simp only [assignedPolicy, Set.mem_iUnion] at hz
    obtain ⟨⟨j, hj⟩, hz⟩ := hz
    have := hmem j
    rw [hj] at this
    exact this hz
  refine ⟨hμ, hincl, ?_⟩
  intro i
  unfold guaranteedStop
  rw [firstIndex_eq _ (σ i) (hmem i) (hmin i), firstIndex_eq _ (σ i)]
  · intro z hz
    simp only [assignedPolicy, Set.mem_iUnion]
    exact ⟨⟨i, rfl⟩, hz⟩
  · intro t ht hsub
    exact hmin i t ht (hsub.trans (hincl t))
