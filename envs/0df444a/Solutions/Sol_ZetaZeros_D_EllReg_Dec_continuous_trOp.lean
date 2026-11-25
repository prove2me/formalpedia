-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.continuous_trOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:08:18.174644+00:00
-- url     : https://prove2.me/submissions/f3098a34-8b6b-45f3-a649-ed9bc0c9022a

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_contDiff_dw

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
theorem _root_.solution (m : ℕ) (b : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (φ : E d → ℂ)
    (hb : ∀ n w, ContDiff ℝ ∞ (b n w)) (hφ : ContDiff ℝ ∞ φ) : Continuous (trOp m b φ) := by
  show Continuous (fun x => ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
    (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * φ y) x)
  refine continuous_finset_sum _ fun n _ => continuous_finset_sum _ fun w _ => continuous_const.mul ?_
  exact (contDiff_dw ((hb n w).mul hφ) _).continuous
end ZetaZeros.D.EllReg.Dec
