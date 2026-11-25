-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cC_smul_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:11.287798+00:00
-- url     : https://prove2.me/submissions/602826b8-3351-48c3-beff-b498e4e52d47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg

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
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {r : ℕ} {m : ℕ∞} {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    {f : B.Mat k r → E} (hf : B.CkOn m (B.GV k r) f) : B.CkOn m (B.GV k r) (fun g => φ g • f g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀
  refine ⟨U, fun g => φ g • f' g, hU, hgU, ?_, fun g hg hgv => by simp only [hff g hg hgv]⟩
  exact ((hφ.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn).smul hf'
end PI.UnitaryCorollaryDerivatives
