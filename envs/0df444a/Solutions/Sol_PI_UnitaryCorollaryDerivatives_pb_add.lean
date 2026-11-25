-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:58.637156+00:00
-- url     : https://prove2.me/submissions/0f3bd6f6-5587-44ec-b8ac-caddf53a95bc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_add


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
theorem _root_.solution {e : ℝ} {f h : B.Mat k r → ℂ} (hf : PG e f) (hh : PG e h) :
    PG e (fun g => f g + h g) := by
  refine ⟨hf.1.add hh.1, fun n => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hf.2 n
  obtain ⟨C₂, hC₂⟩ := hh.2 n
  refine ⟨C₁ + C₂, fun w hw hl g hg => ?_⟩
  have hw' : ∀ x ∈ w, B.inLie k r x.2 := fun x hx => (hw x hx).1
  rw [Dw_add hw' (pb_ck hf.1 _) (pb_ck hh.1 _) g hg, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC₁ w hw hl g hg) (hC₂ w hw hl g hg))
end PI.UnitaryCorollaryDerivatives
