-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.eval_as_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:56.924561+00:00
-- url     : https://prove2.me/submissions/7c555162-3176-421c-a848-5f11847b2a7d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
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
omit [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution (Q : MvPolynomial ι ℂ) (y : ι → ℂ) :
    eval y Q = ∑ s ∈ Q.support, coeff s Q * eval y (monomial s (1 : ℂ)) := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [eval_monomial, eval_monomial, one_mul]
end PositivityTheory.SiegelWeilFormula.KFPB
