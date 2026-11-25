-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_genIndex_trans_a90d09096126
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:50.543137+00:00
-- url     : https://prove2.me/submissions/a7e7d08f-f371-4bca-b970-425d9c966f57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CardQuotientEqGenIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.MatrixSubDegree
theorem _root_.solution {G : Type*} [AddCommGroup G] {A B C : AddSubgroup G}
    (hCA : C ≤ A) (hCB : C ≤ B) (hBC : C.relIndex B ≠ 0) :
    genIndex A C = genIndex A B * genIndex B C := by
  unfold genIndex
  rw [AddSubgroup.relIndex_eq_one.mpr hCA, AddSubgroup.relIndex_eq_one.mpr hCB]
  have h1 := AddSubgroup.relIndex_mul_relIndex C (A ⊓ B) A (le_inf hCA hCB) inf_le_left
  have h2 := AddSubgroup.relIndex_mul_relIndex C (A ⊓ B) B (le_inf hCA hCB) inf_le_right
  have h1' : (A ⊓ B).relIndex A = B.relIndex A := by
    rw [inf_comm]; exact AddSubgroup.inf_relIndex_right B A
  have h2' : (A ⊓ B).relIndex B = A.relIndex B := AddSubgroup.inf_relIndex_right A B
  rw [h1'] at h1
  rw [h2'] at h2
  have hb : (A.relIndex B : ℝ) ≠ 0 := by
    intro h0
    apply hBC
    rw [← h2, Nat.cast_eq_zero.mp h0, mul_zero]
  rw [← h1, ← h2]
  push_cast
  field_simp
end S6.MatrixSubDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
