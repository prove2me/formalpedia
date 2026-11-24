-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:52:41.957798+00:00
-- url     : https://prove2.me/submissions/b3ace93f-e34f-4917-8485-b638cf9e3848

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (m : ℕ∞) :
    B.CkOn m (B.GV k r) f := by
  intro g₀ _
  exact ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn, fun _ _ _ => rfl⟩
end PI.UnitaryCorollaryDerivatives
