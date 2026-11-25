-- Prove2me | solution 1 for PIW.HCFdeg.integrable_cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:24:16.916365+00:00
-- url     : https://prove2.me/submissions/3af9755f-e484-48a0-831d-e0523c6b6df1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_IntegrableCf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [MeasurableSpace G] {μ : Measure G}
namespace PIW.HCFdeg
theorem _root_.solution (π : G →* (H →L[ℂ] H)) (hL2 : ∀ v w : H, MemLp (cf π v w) 2 μ) (v w v' w' : H) :
    Integrable (fun g => cf π v w g * star (cf π v' w' g)) μ := by
  exact (hL2 v w).integrable_mul (p := 2) (q := 2) (hL2 v' w').star
end PIW.HCFdeg
