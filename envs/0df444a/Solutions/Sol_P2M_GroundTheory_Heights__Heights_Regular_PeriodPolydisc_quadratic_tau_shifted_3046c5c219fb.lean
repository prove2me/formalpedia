-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_quadratic_tau_shifted_3046c5c219fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:00.057399+00:00
-- url     : https://prove2.me/submissions/816bf2ca-ab77-40d6-ab9c-bca23136ebbe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_intQuad_cast_144727a14362

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)
namespace GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
theorem _root_.solution (v : Fin g → ℤ) (w : Fin n → ℂ) :
    (fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ (fun k => (v k : ℂ)) =
      (fun k => (v k : ℂ)) ⬝ᵥ P.τ w *ᵥ (fun k => (v k : ℂ)) -
        ∑ i : Fin a, w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) *
          ((intQuad (P.B i) v : ℤ) : ℂ) := by
  simp only [tau0, sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum, smul_mulVec,
    dotProduct_smul, smul_eq_mul, intQuad_cast]
end GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
