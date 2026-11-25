-- Prove2me | solution 1 for P2M_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_absNorm_galois_smul__4af11c9ec6f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:23.700787+00:00
-- url     : https://prove2.me/submissions/d6a2f8bc-22d9-4160-8a3f-78717ee4c2b7

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_AbsNormInvMulDifferent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (E : Type) [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (𝔟 : Ideal (𝓞 E)) :
    Ideal.absNorm (c • 𝔟) = Ideal.absNorm 𝔟 := by
  classical
  rw [Ideal.pointwise_smul_def]
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv 𝔟 _ (MulSemiringAction.toRingEquiv _ (𝓞 E) c) rfl).toEquiv).symm
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
