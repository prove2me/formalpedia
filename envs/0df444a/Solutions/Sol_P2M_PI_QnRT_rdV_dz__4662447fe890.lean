-- Prove2me | solution 1 for P2M_PI_QnRT_rdV_dz__4662447fe890
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:38:50.858018+00:00
-- url     : https://prove2.me/submissions/a3551c1e-92ec-4252-a696-1038e60b5d37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
import Theorems.Thm_PI_QnRT_rdV_dz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (D : Set (Mx k r))
    (f : Mx k r → E) (hf : SmoothLev k r l.castSucc D f) (c : Fin r → ℂ) (hc : c l ≠ 0)
    (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (hD : w1 k r l (c l) * g₁ ∈ D) (κ κ' : ℂ)
    (hκ : κ' = -star κ) :
    RdV (dz l κ κ') f (w1 k r l (c l) * g₁) =
      fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c (Pi.single l (c l * κ)) := by
  subst hκ
  exact rdV_dz l D f hf c hc g₁ hg₁ hD κ
end PI.QnRT
