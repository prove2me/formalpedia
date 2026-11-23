-- Prove2me | solution 1 for PI.TOW.combo_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:39.363813+00:00
-- url     : https://prove2.me/submissions/23686b17-cac6-4939-bee2-c1f69c0fc9af

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
variable {K : Type} [CommRing K] {n' k : ℕ}
namespace PI.TOW
theorem _root_.solution (f₁ f₂ : List (Fin n' × (Fin k × Fin k)) →₀ K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo (f₁ + f₂) G = combo f₁ G + combo f₂ G := by
  unfold combo
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
end PI.TOW
