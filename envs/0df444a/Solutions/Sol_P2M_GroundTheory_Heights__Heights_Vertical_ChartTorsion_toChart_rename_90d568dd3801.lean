-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_toChart_rename_90d568dd3801
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:50.170605+00:00
-- url     : https://prove2.me/submissions/fd8e04e2-a08e-4d37-b724-1dd398a1a180

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
variable {D : Type} [CommRing D] {n : ℕ} (k : ℕ) (P : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)
namespace GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
theorem _root_.solution (p : MvPolynomial (Fin n) D) :
    toChart k P j (rename Sum.inl p) = C (toBase P j p) := by
  induction p using MvPolynomial.induction_on with
  | C d => simp [toChart]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p m hp => simp only [map_mul, hp, rename_X]; simp [toChart]
end GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
