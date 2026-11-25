-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_height_add_ringKrullDim_quotient_le_42493816d064
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:42.811586+00:00
-- url     : https://prove2.me/submissions/8e10ab68-fb7d-4ce4-a5df-2c30310287ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_coheight_d0c00cc69dc4

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) ≤ ringKrullDim B := by
  have : Nonempty (PrimeSpectrum B) := ⟨⟨P, hP⟩⟩
  rw [ringKrullDim_quotient_eq_coheight, PrimeSpectrum.height_eq_orderHeight ⟨P, hP⟩, ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact le_iSup (fun a : PrimeSpectrum B => Order.height a + Order.coheight a) ⟨P, hP⟩
end GroundTheory.Heights₂.Heights
