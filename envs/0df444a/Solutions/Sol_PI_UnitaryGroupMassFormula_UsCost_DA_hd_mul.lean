-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.hd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:17:58.422558+00:00
-- url     : https://prove2.me/submissions/3e05ea3b-7962-4309-9ca6-6352810443db

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_hd_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {t : ℝ}
namespace PI.UnitaryGroupMassFormula.UsCost.DA
theorem _root_.solution {a b c : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {G : ℝ → Matrix (Fin b) (Fin c) ℂ}
    {F' : Matrix (Fin a) (Fin b) ℂ} {G' : Matrix (Fin b) (Fin c) ℂ}
    (hF : HasDerivAt F F' t) (hG : HasDerivAt G G' t) :
    HasDerivAt (fun y => F y * G y) (F' * G t + F t * G') t := by
  rw [hd_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun l _ => (hF i l).mul (hG l j)
end PI.UnitaryGroupMassFormula.UsCost.DA
