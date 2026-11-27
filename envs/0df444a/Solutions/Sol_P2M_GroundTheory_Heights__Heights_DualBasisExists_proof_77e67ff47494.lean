-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualBasisExists_proof_77e67ff47494
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:34.230929+00:00
-- url     : https://prove2.me/submissions/0c47807b-380b-4ce1-9c74-bb1d191a4174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PDualBasisExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeDual_int_fg_d6bcc96c1a9d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeDual_ne_bot_143b76fb3f48

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
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace DualBasisExists
theorem _root_.solution : DualBasisExists.Statement := by
  intro K _ _ r F
  classical
  let M : Submodule ℤ (Fin (r + 1) → K) := (latticeDual F.lattice).restrictScalars ℤ
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr (latticeDual_int_fg F)
  have : Module.Free ℤ M := inferInstance
  obtain ⟨ψ, hψ, hψ0⟩ := latticeDual_ne_bot F
  have : Nontrivial M := ⟨⟨⟨ψ, hψ⟩, 0, fun h ↦ hψ0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank ℤ M := Module.finrank_pos
  obtain ⟨N, hN⟩ : ∃ N, Module.finrank ℤ M = N + 1 :=
    ⟨Module.finrank ℤ M - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  let bas := Module.finBasisOfFinrankEq ℤ M hN
  refine ⟨N, fun i ↦ (bas i : Fin (r + 1) → K), ?_, ?_⟩
  · exact bas.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  · have : Set.range (fun i ↦ (bas i : Fin (r + 1) → K)) = M.subtype '' Set.range bas := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, bas.span_eq, Submodule.map_top, Submodule.range_subtype]
end DualBasisExists
end GroundTheory.Heights₂.Heights
