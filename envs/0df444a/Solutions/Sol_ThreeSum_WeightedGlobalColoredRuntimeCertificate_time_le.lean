-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredRuntimeCertificate.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T03:54:15.826461+00:00
-- url     : https://prove2.me/submissions/94320b1a-4a5b-4195-8b31-2619f754dbb7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Definitions.Def_Submission_Weighted_Global_TernaryColoredQueryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeCertificate
import Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeCertificate_fits
import Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeCertificate_query_bound
import Theorems.Thm_Light_Compiler_Holds_output
import Theorems.Thm_ThreeSum_LightPrimality_time_le_uniform
import Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_time_le_uniform
import Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_time_le_uniform
import Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_full_exponent_lt
import Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_local_factor_polynomial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocation_Allocation_fits
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_good
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_F_gt_one
import Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_local_nonempty


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredRuntimeCertificate
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
namespace ThreeSum.WeightedGlobalColoredRuntimeCertificate
theorem _root_.solution (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    WeightedGlobalActualColoredRuntime.time (k:=P.k) P.maps P.output
      (state P n free menu c A B C initial) P.allocation.E κ P.H n≤P.colorTime n := by
  have hf:=fits P n free menu c A B C initial hmeta hinputs
  exact WeightedGlobalActualGlobalQueryRuntime.time_le_uniform (b:=localFactor P.m) (Hdet:=P.H) hf
    P.K_pos P.k_pos P.good hinputs.1 (by have := P.F_gt_one;omega) le_rfl le_rfl
    (P.local_nonempty false) (P.local_nonempty true)
    (query_bound P n free menu c A B C initial hmeta hinputs.1) 19 3 (local_factor_polynomial P.m)
    (full_exponent_lt P.large 19 3 P.good P.overhead).le
end ThreeSum.WeightedGlobalColoredRuntimeCertificate
