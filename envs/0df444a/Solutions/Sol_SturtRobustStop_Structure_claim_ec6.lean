-- Prove2me | solution 1 for SturtRobustStop.Structure.claim_ec6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:12:30.38494+00:00
-- url     : https://prove2.me/submissions/5d07431e-7a9c-417a-aa66-68e38fc3a3f1

import Definitions.Def_SturtRobustStop_Structure_Pruning

open SturtRobustStop.Structure in
theorem solution {T N d : ℕ} (D : SturtRobustStop.Structure.Model T N d)
    (μ : SturtRobustStop.Structure.Policy T (SturtRobustStop.Structure.State d))
    (hμ : SturtRobustStop.Structure.TerminalFeasible D μ) :
    ∀ t : Fin T, (SturtRobustStop.Structure.assignedPolicy D
      (SturtRobustStop.Structure.canonicalAssignment D μ hμ)).stop t ⊆ μ.stop t := by
  classical
  intro t z hz
  simp only [SturtRobustStop.Structure.assignedPolicy, Set.mem_iUnion] at hz
  obtain ⟨⟨i, hi⟩, hz⟩ := hz
  have hmem := Finset.min'_mem (SturtRobustStop.Structure.guaranteedTimes D μ i)
    (SturtRobustStop.Structure.guaranteedTimes_nonempty D μ hμ i)
  unfold SturtRobustStop.Structure.guaranteedTimes at hmem
  rw [Finset.mem_filter] at hmem
  have hsub : SturtRobustStop.Structure.box D i t ⊆ μ.stop t := by
    rw [← hi]
    exact hmem.2
  exact hsub hz
