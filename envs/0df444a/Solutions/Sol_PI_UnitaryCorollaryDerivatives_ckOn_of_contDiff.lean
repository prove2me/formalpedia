-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:17.513906+00:00
-- url     : https://prove2.me/submissions/aeea2e61-0c66-4558-9ad7-6483751c548c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_WeightBoundMultiplicative

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞}
    {f : B.Mat k r → E} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) : B.CkOn m (B.GV k r) f := by
  intro g₀ _
  exact ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn, fun _ _ _ => rfl⟩
end PI.UnitaryCorollaryDerivatives
