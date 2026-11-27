-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLineExists_proof_e05e923cf719
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:35.709194+00:00
-- url     : https://prove2.me/submissions/2c1fcaa5-e8f4-4c6f-8402-053b04e5aba7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLatticeLineExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLine_quad_point_4515c0280d44
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLine_conj_point_933b0adfa5ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLine_herm_conj_f362b5512beb

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
open NumberField Matrix
open scoped ComplexOrder ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace LatticeLineExists
theorem _root_.solution (h : OneBlockPoints.Statement) : LatticeLineExists.Statement := by
  intro K _ _ r N F φ hφ
  obtain ⟨-, -, hrec⟩ := h K r N F φ hφ
  choose R hR using hrec
  refine ⟨LatticeLine.line F φ R, rfl, ?_, ?_⟩
  · intro s w _
    show Real.sqrt ((LatticeLine.quad F φ R (latticePoint φ s w ()) +
      LatticeLine.quad F φ R (fun b ↦ starRingEnd ℂ (latticePoint φ s w () b))) / 2) = _
    rw [LatticeLine.conj_point, LatticeLine.quad_point F φ R hR, LatticeLine.quad_point F φ R hR,
      LatticeLine.herm_conj]
    congr 1
    ring
  · intro z _
    show Real.sqrt ((LatticeLine.quad F φ R (fun b ↦ starRingEnd ℂ (z () b)) +
      LatticeLine.quad F φ R (fun b ↦ starRingEnd ℂ (starRingEnd ℂ (z () b)))) / 2) =
      Real.sqrt ((LatticeLine.quad F φ R (z ()) +
        LatticeLine.quad F φ R (fun b ↦ starRingEnd ℂ (z () b))) / 2)
    simp only [Complex.conj_conj]
    rw [add_comm]
end LatticeLineExists
end GroundTheory.Heights₂.Heights
