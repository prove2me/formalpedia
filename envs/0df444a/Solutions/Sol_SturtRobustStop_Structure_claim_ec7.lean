-- Prove2me | solution 1 for SturtRobustStop.Structure.claim_ec7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:08:41.243687+00:00
-- url     : https://prove2.me/submissions/cdbe27d0-e511-43c6-9c60-94d7007da4f1

import Definitions.Def_SturtRobustStop_Structure_Pruning

namespace Aux_Q01_claim_ec7
open SturtRobustStop.Structure

theorem firstIndex_eq_some {T : ℕ} (p : Fin T → Prop) (t0 : Fin T) (h0 : p t0)
    (hmin : ∀ t, p t → t0 ≤ t) : firstIndex p = some t0 := by
  unfold firstIndex
  dsimp only
  split
  · rename_i h
    congr 1
    apply le_antisymm
    · exact Finset.min'_le _ _ (by simp [h0])
    · exact Finset.le_min' _ _ _ (fun t ht => hmin t (by simpa using ht))
  · rename_i h
    exact absurd ⟨t0, by simp [h0]⟩ h

end Aux_Q01_claim_ec7

open SturtRobustStop.Structure in
theorem solution {T N d : ℕ} (D : Model T N d) (μ : Policy T (State d))
    (hμ : TerminalFeasible D μ) :
    ∀ i : Fin N, guaranteedStop D (assignedPolicy D (canonicalAssignment D μ hμ)) i =
      guaranteedStop D μ i := by
  intro i
  have hσmem : ∀ j, box D j (canonicalAssignment D μ hμ j) ⊆
      μ.stop (canonicalAssignment D μ hμ j) := by
    intro j
    have h := Finset.min'_mem (guaranteedTimes D μ j) (guaranteedTimes_nonempty D μ hμ j)
    simp only [guaranteedTimes, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hmin : ∀ t, box D i t ⊆ μ.stop t → canonicalAssignment D μ hμ i ≤ t := by
    intro t ht
    have hm : t ∈ guaranteedTimes D μ i := by simp [guaranteedTimes, ht]
    exact Finset.min'_le _ _ hm
  have hsub : ∀ t, (assignedPolicy D (canonicalAssignment D μ hμ)).stop t ⊆ μ.stop t := by
    intro t z hz
    simp only [assignedPolicy, Set.mem_iUnion] at hz
    obtain ⟨⟨j, hj⟩, hzj⟩ := hz
    have := hσmem j
    rw [hj] at this
    exact this hzj
  have hself : box D i (canonicalAssignment D μ hμ i) ⊆
      (assignedPolicy D (canonicalAssignment D μ hμ)).stop (canonicalAssignment D μ hμ i) := by
    intro z hz
    simp only [assignedPolicy, Set.mem_iUnion]
    exact ⟨⟨i, rfl⟩, hz⟩
  unfold guaranteedStop
  rw [Aux_Q01_claim_ec7.firstIndex_eq_some _ (canonicalAssignment D μ hμ i) hself
      (fun t ht => hmin t (ht.trans (hsub t))),
    Aux_Q01_claim_ec7.firstIndex_eq_some _ (canonicalAssignment D μ hμ i) (hσmem i) hmin]
