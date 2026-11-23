-- Prove2me | solution 1 for PI.StabBigW.g_mid_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:37.535044+00:00
-- url     : https://prove2.me/submissions/293020cb-600e-4ae0-b3f3-f0e5883e40f6

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv

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
theorem _root_.solution (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k)
    (hi : i.val < r ∨ r + k < i.val) : bigCell k r c μ i j = 0 := by
  have h0 : ¬ j.val < r := by omega
  have h3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k) := by omega
  simp only [bigCell, dif_neg h0, dif_pos hj2, dif_neg h3]
end PI.StabBigW
