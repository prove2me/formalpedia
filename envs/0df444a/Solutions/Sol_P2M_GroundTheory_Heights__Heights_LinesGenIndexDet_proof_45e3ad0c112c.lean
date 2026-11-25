-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesGenIndexDet_proof_45e3ad0c112c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:43.405422+00:00
-- url     : https://prove2.me/submissions/32855075-3dcc-4592-9fb6-678287e3e006

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexDet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexDet_span_basis_isLattice_3a75cc8017cc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open KLinesGenIndexDet
namespace GroundTheory.Heights₂.Heights
namespace LinesGenIndexDet
theorem _root_.solution (h1 : LinesLatticeBasis.Statement) : LinesGenIndexDet.Statement := by
  intro V _ _ _ ι _ _ bA bB A B hA hB
  set MA := Submodule.span ℤ (Set.range bA)
  set MB := Submodule.span ℤ (Set.range bB)
  have := span_basis_isLattice bA
  have := span_basis_isLattice bB
  obtain ⟨bE, hE⟩ := h1 V ι (Module.finrank_eq_card_basis bA).symm (MA ⊓ MB) inferInstance
  have hAB : A ⊓ B = AddSubgroup.closure (Set.range bE) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, ← hE, hA, hB,
      ← Submodule.span_int_eq_addSubgroupClosure, ← Submodule.span_int_eq_addSubgroupClosure]
    rfl
  have hBA : B ⊓ A = AddSubgroup.closure (Set.range bE) := by rw [inf_comm, hAB]
  have e1 : ((B.relIndex A : ℕ) : ℚ) = |bA.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bA hBA hA
  have e2 : ((A.relIndex B : ℕ) : ℚ) = |bB.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bB hAB hB
  have hne : bB.det bE ≠ 0 := (bB.isUnit_det bE).ne_zero
  have key : (B.relIndex A : ℚ) / (A.relIndex B : ℚ) = |bA.det bB| := by
    rw [e1, e2, ← bA.det_mul_det bB bE, abs_mul, mul_div_assoc, div_self (abs_ne_zero.mpr hne),
      mul_one]
  unfold genIndex
  have := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at this
  exact this
end LinesGenIndexDet
end GroundTheory.Heights₂.Heights
