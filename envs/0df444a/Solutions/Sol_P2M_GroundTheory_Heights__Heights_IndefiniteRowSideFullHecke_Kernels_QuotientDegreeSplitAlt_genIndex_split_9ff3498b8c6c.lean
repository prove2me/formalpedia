-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_genIndex_split_9ff3498b8c6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:24.07536+00:00
-- url     : https://prove2.me/submissions/174c3434-7aa0-43eb-b57a-c9727e032a6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RelIndexSplitOfLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_relIndex_split_of_le_c4f5536e3b50

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
open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.QuotientDegreeSplitAlt
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.QuotientDegreeSplitAlt
theorem _root_.solution {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (π : G →+ G')
    (A C : AddSubgroup G) (hpos : 0 < genIndex A C) :
    genIndex A C = genIndex (A ⊓ π.ker) (C ⊓ π.ker) * genIndex (A.map π) (C.map π) := by
  have hDA : (A ⊓ C).map π ≤ A.map π := AddSubgroup.map_mono inf_le_left
  have hDC : (A ⊓ C).map π ≤ C.map π := AddSubgroup.map_mono inf_le_right
  have hA : C.relIndex A = (A ⊓ C).relIndex (A ⊓ π.ker) * (((A ⊓ C).map π).relIndex
      (A.map π ⊓ C.map π) * (C.map π).relIndex (A.map π)) := by
    rw [← AddSubgroup.inf_relIndex_left A C, relIndex_split_of_le π (inf_le_left : A ⊓ C ≤ A),
      inf_comm (A.map π), AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left hDC]
  have hC : A.relIndex C = (A ⊓ C).relIndex (C ⊓ π.ker) * (((A ⊓ C).map π).relIndex
      (A.map π ⊓ C.map π) * (A.map π).relIndex (C.map π)) := by
    rw [← AddSubgroup.inf_relIndex_right A C, relIndex_split_of_le π (inf_le_right : A ⊓ C ≤ C),
      AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left hDA]
  have hW1 : (C ⊓ π.ker).relIndex (A ⊓ π.ker) = (A ⊓ C).relIndex (A ⊓ π.ker) := by
    rw [← AddSubgroup.inf_relIndex_right (C ⊓ π.ker), ← AddSubgroup.inf_relIndex_right (A ⊓ C)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    tauto
  have hW2 : (A ⊓ π.ker).relIndex (C ⊓ π.ker) = (A ⊓ C).relIndex (C ⊓ π.ker) := by
    rw [← AddSubgroup.inf_relIndex_right (A ⊓ π.ker), ← AddSubgroup.inf_relIndex_right (A ⊓ C)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    tauto
  have he : ((((A ⊓ C).map π).relIndex (A.map π ⊓ C.map π) : ℕ) : ℝ) ≠ 0 := by
    intro h0
    have hz : genIndex A C = 0 := by
      unfold genIndex
      rw [hA]
      push_cast
      rw [h0]
      simp
    linarith
  unfold genIndex
  rw [hA, hC, hW1, hW2]
  push_cast
  rw [div_mul_div_comm, mul_left_comm (((A ⊓ C).relIndex (A ⊓ π.ker) : ℕ) : ℝ),
    mul_left_comm (((A ⊓ C).relIndex (C ⊓ π.ker) : ℕ) : ℝ), mul_div_mul_left _ _ he]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.QuotientDegreeSplitAlt
