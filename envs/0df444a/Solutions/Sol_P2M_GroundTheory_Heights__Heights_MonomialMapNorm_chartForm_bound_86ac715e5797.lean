-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartForm_bound_86ac715e5797
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:32.836587+00:00
-- url     : https://prove2.me/submissions/236b05fa-d62a-4a91-b049-6afe8524ca3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_chartMonomial_ne_zero_74ae91588762

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {A : HermLine n} {s : IntegralSection P A.deg} (hs : s.SupNormLE A 0)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} {d : ι → ℕ}
    {e : MvPolynomial (Coord n) ℤ} (he : IsChartForm P A.deg s.num s.den c d e) (hcz : ∀ k, z k (c k) ≠ 0) :
    ‖evalCone z e‖ ≤ ‖evalCone z (chartMonomial c d)‖ * A.metric z := by
  have h := hs z hz c d e he hcz
  rwa [Real.exp_zero, div_le_one (mul_pos (norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hcz d))
    (A.metric_pos z hz.1))] at h
end GroundTheory.Heights₂.Heights.MonomialMapNorm
