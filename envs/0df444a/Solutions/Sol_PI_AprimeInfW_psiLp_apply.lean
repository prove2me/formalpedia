-- Prove2me | solution 1 for PI.AprimeInfW.psiLp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:14.492428+00:00
-- url     : https://prove2.me/submissions/8c027105-0d3d-459d-aeee-f3957c98831b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MpOfIsomProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix ComplexConjugate
namespace PI.AprimeInfW
theorem _root_.solution {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (z : EuclideanSpace ℝ η × EuclideanSpace ℝ η) : psiLp H z = reim (Complex.I • H z.1 + H z.2) := rfl
end PI.AprimeInfW
