-- Prove2me | solution 1 for PI.TOW.combo_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:39.340556+00:00
-- url     : https://prove2.me/submissions/ff6fc464-fbba-41c5-88f4-22cb1c77b7fd

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
theorem _root_.solution (a : K) (f : List (Fin n' × (Fin k × Fin k)) →₀ K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo (a • f) G = a • combo f G := by
  unfold combo
  rw [Finsupp.sum_smul_index' (h := fun (l : List (Fin n' × (Fin k × Fin k))) (c : K) => c • opWord l G)
    (fun _ => zero_smul _ _), Finsupp.smul_sum]
  exact Finsupp.sum_congr fun l _ => by rw [smul_eq_mul, mul_smul]
end PI.TOW
