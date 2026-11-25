-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.prod_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:29.895519+00:00
-- url     : https://prove2.me/submissions/5b882f7d-2179-4853-8c09-3c2c76c5a73d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_norm_sq_euc
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
theorem _root_.solution {b : ℝ} (hb : 0 < b) (u : EuclideanSpace ℝ ι) (A : ι → ℂ) :
    ∏ i, (A i * (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * cexp ((2 * Real.pi * I * u i) ^ 2 / (4 * b)))) =
      (∏ i, A i) * kG b ^ Fintype.card ι * (Real.exp (-(Real.pi ^ 2 / b * ‖u‖ ^ 2)) : ℂ) := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← Complex.exp_sum, ← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, norm_sq_euc]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring_nf
  rw [I_sq]
  ring
end PositivityTheory.SiegelWeilFormula.KFPB
