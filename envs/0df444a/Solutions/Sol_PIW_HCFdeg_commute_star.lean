-- Prove2me | solution 1 for PIW.HCFdeg.commute_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:34:05.480995+00:00
-- url     : https://prove2.me/submissions/d6c2f523-5230-4706-b3ca-bd3db6018bcd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_CommuteStar
import Theorems.Thm_PIW_HCFdeg_adjoint_rep

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
open scoped InnerProductSpace ComplexStarModule
open ContinuousLinearMap
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : G →* (H →L[ℂ] H))
namespace PIW.HCFdeg
theorem _root_.solution (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (T : H →L[ℂ] H) (hT : ∀ g, Commute T (π g))
    (g : G) : Commute (star T) (π g) := by
  have h1 : star (π g⁻¹) = π g := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_rep π hπ, inv_inv]
  have h2 : T * π g⁻¹ = π g⁻¹ * T := hT g⁻¹
  show star T * π g = π g * star T
  calc star T * π g = star T * star (π g⁻¹) := by rw [h1]
    _ = star (π g⁻¹ * T) := by rw [star_mul]
    _ = star (T * π g⁻¹) := by rw [h2]
    _ = star (π g⁻¹) * star T := by rw [star_mul]
    _ = π g * star T := by rw [h1]
end PIW.HCFdeg
