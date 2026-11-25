-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.mono_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:26:07.48639+00:00
-- url     : https://prove2.me/submissions/a9e233fb-6eed-461c-8f39-0d93f8425475

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_norm_sq_euc
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_inner_euc
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_circle_smul
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_eval_mono
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
theorem _root_.solution (b : ℝ) (s : ι →₀ ℕ) (u : EuclideanSpace ℝ ι) (x : ι → ℝ) :
    𝐞 (inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) u) •
      (eval (fun i => (((WithLp.toLp 2 x : EuclideanSpace ℝ ι) i : ℝ) : ℂ)) (monomial s (1 : ℂ)) *
        (Real.exp (-(b * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2)) : ℂ)) =
      ∏ i, phi b (s i) (2 * Real.pi * I * u i) (x i) := by
  rw [circle_smul, eval_mono, inner_euc, norm_sq_euc]
  simp only [phi, Finset.prod_mul_distrib, ← Complex.exp_sum]
  rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end PositivityTheory.SiegelWeilFormula.KFPB
