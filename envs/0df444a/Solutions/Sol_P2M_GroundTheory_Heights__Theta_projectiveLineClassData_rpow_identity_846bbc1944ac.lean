-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_rpow_identity_846bbc1944ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:26.901533+00:00
-- url     : https://prove2.me/submissions/53858105-b3cd-4d83-a51d-37604c078e53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution {n q y : ℝ} (hn : 0 < n) (hq : 0 < q) (hy : 0 < y) (s : ℝ) :
    (n ^ 2 * q / (2 * y)) ^ (-s) = (2 / q) ^ s * (y ^ s / n ^ (2 * s)) := by
  rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
  have h : (n ^ 2 * q / (2 * y))⁻¹ = (2 / q) * (y / n ^ 2) := by
    rw [inv_div]
    field_simp
  rw [h, Real.mul_rpow (by positivity) (by positivity), Real.div_rpow hy.le (by positivity),
    show (2 : ℝ) * s = ((2 : ℕ) : ℝ) * s by norm_num, Real.rpow_natCast_mul hn.le]
end GroundTheory.Heights₂.Theta.projectiveLineClassData
