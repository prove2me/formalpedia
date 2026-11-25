-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_relIndex_split_of_le_c4f5536e3b50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:34.526266+00:00
-- url     : https://prove2.me/submissions/f30f80b0-39a5-41e2-8e3c-53b8644d80dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RelIndexSplitOfLe

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
    {A C : AddSubgroup G} (hCA : C ≤ A) :
    C.relIndex A = C.relIndex (A ⊓ π.ker) * (C.map π).relIndex (A.map π) := by
  have h1 : (C.map π).relIndex (A.map π) = (C ⊔ π.ker).relIndex A := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq]
  have hmod : (A ⊓ π.ker) ⊔ C = (C ⊔ π.ker) ⊓ A := by
    ext x
    simp only [AddSubgroup.mem_sup, AddSubgroup.mem_inf]
    constructor
    · rintro ⟨y, ⟨hyA, hyW⟩, z, hz, rfl⟩
      exact ⟨⟨z, hz, y, hyW, add_comm z y⟩, add_mem hyA (hCA hz)⟩
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hA⟩
      refine ⟨z, ⟨?_, hz⟩, y, hy, add_comm z y⟩
      have hz' : z = (y + z) - y := by abel
      rw [hz']
      exact sub_mem hA (hCA hy)
  have h2 : C.relIndex ((C ⊔ π.ker) ⊓ A) = C.relIndex (A ⊓ π.ker) := by
    rw [← hmod, AddSubgroup.relIndex_sup_right]
  rw [h1, ← h2, AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left le_sup_left]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.QuotientDegreeSplitAlt
