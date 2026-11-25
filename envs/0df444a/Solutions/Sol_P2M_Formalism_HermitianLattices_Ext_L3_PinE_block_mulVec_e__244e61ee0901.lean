-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_PinE_block_mulVec_e__244e61ee0901
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:28.287431+00:00
-- url     : https://prove2.me/submissions/33b3c03f-ac51-4f99-8daa-692e36329880

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinE
variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.HermitianLattices.Ext.L3.PinE
theorem _root_.solution (X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) *ᵥ e₀ = e₀ := by
  unfold e₀
  rw [mulVec_single_one]
  ext i
  rcases i with ⟨⟩ | i <;> simp
end Formalism.HermitianLattices.Ext.L3.PinE
