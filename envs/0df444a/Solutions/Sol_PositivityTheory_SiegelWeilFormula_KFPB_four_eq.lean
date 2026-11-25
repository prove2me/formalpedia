-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.four_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:13.697467+00:00
-- url     : https://prove2.me/submissions/e6925da1-d46d-4ce6-ab3a-b13dc9cd1464

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_Kf_contDiff
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_Kf_line
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_line_poly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap InnerProductSpace FourierTransform
open MeasureTheory
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution {c : ℝ} (hc : 0 < c) (N : ℕ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (H : ∀ ξ : EuclideanSpace ℝ ι, ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z : ℂ,
      ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) =
        Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (8 * c)) * p.eval z) :
    ∃ Q : MvPolynomial ι ℂ, Q.totalDegree ≤ N ∧ ∀ η, 𝓕 (gW c h) η =
      MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(Real.pi ^ 2 / (2 * c) * ‖η‖ ^ 2)) : ℂ) := by
  obtain ⟨Q, hQ, hKQ⟩ := line_poly N (Kf c h) (Kf_contDiff hc.le h N) (Kf_line hc N h H)
  refine ⟨Q, hQ, fun η => ?_⟩
  rw [← hKQ, Kf, mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    Complex.ofReal_one, one_mul]
end PositivityTheory.SiegelWeilFormula.KFPB
