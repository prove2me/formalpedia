-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.integrable_poly_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:20.360036+00:00
-- url     : https://prove2.me/submissions/d5577abb-c2fe-47d4-a1a5-1829c844ecd5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_eval_as_sum
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integrable_mono0
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_eq
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_zero
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_pow_quad
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_pk_deg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped FourierTransform
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KLI (J pk J_eq J_zero intg_pow_quad pk_deg)
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution {ι : Type} [Fintype ι] (b : ℝ) (hb : 0 < b) (Q : MvPolynomial ι ℂ) :
    MeasureTheory.Integrable (fun η : EuclideanSpace ℝ ι =>
      MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) := by
  have e : (fun η : EuclideanSpace ℝ ι =>
      MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) = fun η =>
      ∑ s ∈ Q.support, coeff s Q *
        (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) := by
    funext η
    rw [eval_as_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun s _ => (integrable_mono0 hb s).const_mul _
end PositivityTheory.SiegelWeilFormula.KFPB
