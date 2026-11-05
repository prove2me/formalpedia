-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation.prepare_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:46:17.527198+00:00
-- url     : https://prove2.me/submissions/179d3dbd-b79d-4e32-a443-a45fc5fb89a1

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredLoopAllocation_beta_eq_drift
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredLoopAllocation_drift_scale_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixPrepareAllocation_allocated_initial


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation
theorem _root_.solution (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hA : A.length≤n) (j : ℕ) (hj : j<rounds P n) :
    WeightedGlobalArenaPrefixPrepare.envelope
      (WeightedGlobalArenaPrefixPrepare.inputs P.p P.m P.F j (J P n) n (initialBudget P n A)
        (P.p^(2*P.K)) (9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K)
        (2^(fixedPi P.m 2*P.K)) (input P n free A B C) P.output)≤
      (input P n free A B C).capacity := by
  rw [beta_eq_drift]
  have hh := WeightedGlobalArenaPrefixPrepareAllocation.allocated_initial P.maps P.threshold P.cap P.M
    P.radix P.K P.H P.drift P.scale n (n^κ) j (A.length*2^(J P n)) P.allocation
    (input P n free A B C) P.output
    (show j+1≤Nat.clog P.M (n^2) by change j<Nat.clog P.M (n^2) at hj;omega)
    (show (input P n free A B C).capacity=capacity P.allocation.D P.allocation.E (n+n^κ) from rfl)
    (drift_scale_pos P) (Nat.mul_le_mul_right _ hA)
  exact hh
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation
