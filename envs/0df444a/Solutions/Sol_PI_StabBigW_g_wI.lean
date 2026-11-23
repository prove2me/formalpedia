-- Prove2me | solution 1 for PI.StabBigW.g_wI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:32.689803+00:00
-- url     : https://prove2.me/submissions/d597ccea-656e-4909-9cd7-1595e8c926ff

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_wI_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace PI.StabBigW
theorem _root_.solution (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t : Fin (k + 1)) :
    bigCell k r c μ (wI k r s) (wI k r t) = μ s t := by
  have hs := s.isLt
  have ht := t.isLt
  have h1 : ¬ (wI k r t).val < r := by rw [wI_val]; omega
  have h2 : (wI k r t).val ≤ r + k := by rw [wI_val]; omega
  have h3 : r ≤ (wI k r s).val ∧ (wI k r s).val ≤ r + k := by rw [wI_val]; omega
  simp only [bigCell, dif_neg h1, dif_pos h2, dif_pos h3]
  exact congrArg₂ μ (Fin.ext (by show r + s.val - r = s.val; omega))
    (Fin.ext (by show r + t.val - r = t.val; omega))
end PI.StabBigW
