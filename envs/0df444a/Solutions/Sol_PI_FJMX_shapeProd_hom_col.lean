-- Prove2me | solution 1 for PI.FJMX.shapeProd_hom_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:53:00.612499+00:00
-- url     : https://prove2.me/submissions/78168279-1470-42a6-ab4c-ccba8467ffaa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Theorems.Thm_PI_FJMX_shape_sum
import Theorems.Thm_PI_FJMX_leadT_hom_col
import Theorems.Thm_PI_FJMX_shapeProd_hom_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s m k : ℕ}
namespace PI.FJMX
theorem _root_.solution (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (j₀ : Fin k)
    (hw : ∀ i j, w (ρ i, κ j) = if j = j₀ then 1 else 0) (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) :
    IsWeightedHomogeneous w (shapeProd (varMat ρ κ) α) (α.getD j₀.val 0) := by
  have := shapeProd_hom_of (varMat ρ κ) w α _ (leadT_hom_col ρ κ w j₀ hw)
  rwa [shape_sum α hα] at this
end PI.FJMX
