-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:58.399145+00:00
-- url     : https://prove2.me/submissions/ddedb091-c34a-4c05-a1a3-46a8abdc3361

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_GfPolyA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_cmul
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_mulc
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_sum
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_X

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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {N : ℕ}
namespace PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
theorem _root_.solution (H : Matrix (Fin N) (Fin N) ℂ) (v w : Fin N → ℂ) :
    IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => herm H (g *ᵥ v) w) := by
  simp only [herm, dotProduct, mulVec]
  exact pd_sum _ _ fun i _ => pd_cmul _ (pd_sum _ _ fun j _ => pd_cmul _
    (pd_sum _ _ fun l _ => pd_mulc _ (pd_X j l)))
end PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
