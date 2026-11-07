-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.kt19_family_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:15:16.750313+00:00
-- url     : https://prove2.me/submissions/2313a4d3-43da-46fc-b8d4-a783cf8e898d

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_dimension
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace KT19ReedSolomon
open scoped BigOperators
private theorem keptPunctureLocation_card (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    Fintype.card (KeptPunctureLocation p k) = p - k := by
  simpa using keptPunctureLocations_card p k hkp
end KT19ReedSolomon
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution (p l k : Nat) [Fact p.Prime]
    (h : Admissible p l k) :
    kt19Length p k = p - k ∧
      kt19LogicalDimension p l k = k ∧
        kt19SafeDistance p l k ≥ l - k := by
  rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkp : k ≤ p := hkl.trans hlp
  have hkm : k ≤ p - l := by omega
  have hlength : kt19Length p k = p - k := by
    simp [kt19Length, Length, keptPunctureLocation_card p k hkp]
  refine ⟨hlength, ?_, by simp [kt19SafeDistance]⟩
  rw [kt19LogicalDimension, hlength,
    shortenedReedSolomonCode_dimension p l k hkp hkl hlp,
    shortenedReedSolomonCode_dimension p (p - l) k hkp hkm (Nat.sub_le _ _)]
  omega
end QEC.Coding.KT19ReedSolomon
