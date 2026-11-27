-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_levels_exist__cf4cc5b3e47d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:03.155993+00:00
-- url     : https://prove2.me/submissions/b0d44b27-dad4-4152-a8b8-499020c153ff

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isS_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isNU_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.LevelsExist := by
  intro o _ _ r k
  exact ⟨⟨(PG r (upUniG _ k)).comap (red o (Idx r k)), (PG r ⊤).comap (red o (Idx r k)),
    (upUniG _ k).comap (red o (Fin k)),
    fun x => by rw [Subgroup.mem_comap, isNU_iff], fun x => by rw [Subgroup.mem_comap, isS_iff],
    fun x => Iff.rfl⟩⟩
end Formalism.FourierDecayAlt.P
