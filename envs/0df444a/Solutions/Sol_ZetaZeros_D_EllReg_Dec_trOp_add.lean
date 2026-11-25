-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.trOp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:16:05.920563+00:00
-- url     : https://prove2.me/submissions/72c2f7c5-2e48-4d35-9665-1b9c7db710d3

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_dw_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.Dec
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.Dec
theorem _root_.solution (m : ℕ) (b1 b2 : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (φ : E d → ℂ)
    (h1 : ∀ n w, ContDiff ℝ ∞ (b1 n w)) (h2 : ∀ n w, ContDiff ℝ ∞ (b2 n w)) (hφ : ContDiff ℝ ∞ φ) (x : E d) :
    trOp m (fun n w y => b1 n w y + b2 n w y) φ x = trOp m b1 φ x + trOp m b2 φ x := by
  simp only [trOp]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (fun y => (b1 n w y + b2 n w y) * φ y) = fun y => b1 n w y * φ y + b2 n w y * φ y := by
    funext y
    ring
  rw [e, dw_add ((h1 n w).mul hφ) ((h2 n w).mul hφ)]
  simp only [mul_add]
end ZetaZeros.D.EllReg.Dec
