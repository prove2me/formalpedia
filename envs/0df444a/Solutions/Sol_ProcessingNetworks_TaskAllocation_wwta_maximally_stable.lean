-- Prove2me | solution 1 for ProcessingNetworks.TaskAllocation.wwta_maximally_stable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:42:21.716607+00:00
-- url     : https://prove2.me/submissions/8b6fe27d-ea35-4926-96dd-3988c05e8df5

import Mathlib
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel
import Definitions.Def_ProcessingNetworks_TaskAllocation_FluidModel
import Theorems.Thm_ProcessingNetworks_TaskAllocation_wwta_fluid_stable_of_load_condition

open ProcessingNetworks.TaskAllocation in
theorem solution
    {L K : ℕ} [Nonempty (Fin K)] (dat : TaskAllocationData L K)
    {Policy : Type*} (PolicyStable : Policy → Prop) (wwta : Policy)
    (hnecessary : (∃ p, PolicyStable p) →
      ∃ lam : Fin L → Fin K → ℝ, (∀ ℓ k, 0 ≤ lam ℓ k) ∧
        (∀ ℓ, ∑ k, lam ℓ k = dat.nu ℓ) ∧ (∀ k, ∑ ℓ, dat.m ℓ k * lam ℓ k < 1))
    (hwwta_of_load : WWTAFluidStable dat → PolicyStable wwta)
    (hex : ∃ p, PolicyStable p) :
    PolicyStable wwta :=
  hwwta_of_load (wwta_fluid_stable_of_load_condition dat (hnecessary hex))


