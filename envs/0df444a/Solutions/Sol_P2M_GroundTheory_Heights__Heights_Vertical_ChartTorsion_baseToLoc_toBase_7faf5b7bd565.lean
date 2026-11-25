-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_baseToLoc_toBase_7faf5b7bd565
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:48.707039+00:00
-- url     : https://prove2.me/submissions/5bcf410c-84fe-47d0-a905-ddb285ecf331

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
    baseToLoc k P j (toBase P j p) = toLoc k P j (rename Sum.inl p) := by
  simp [baseToLoc, toBase, quotToLoc_mk]
end GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
