-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbFnVanishBlock_proof_30f55825ab61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:05.834804+00:00
-- url     : https://prove2.me/submissions/c44442da-2f52-4da9-b2ba-8e232ccef3f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbFnVanishBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_block_vars_mem_572dc42ada6f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace HilbFnVanishBlock
theorem _root_.solution : HilbFnVanishBlock.Statement.{u} := by
  intro F _ K _ _ ι _ Q k hX m hm
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece Q (fun k => (m k).toNat) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
      have hfQ : f ∈ Q := mem_of_block_vars_mem Q k hX _ (by omega) f hf
      simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr hfQ
    rw [hbot, finrank_bot]
    rfl
  · rfl
end HilbFnVanishBlock
end GroundTheory.Heights₂.Heights.NumbersDVR
