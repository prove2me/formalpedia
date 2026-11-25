-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.integrable_gaussian_moment
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:12:28.20198+00:00
-- url     : https://prove2.me/submissions/11096c01-0fa6-42b3-ae23-8bc72e00f159

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_GaussianMomentRealCoords
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_mer_symm
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_gaussian_moment_real_coords
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_poly2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
namespace PositivityTheory.SiegelWeilFormula.KLI
theorem _root_.solution (sg : ℤˣ) (t z ξ : ℂ) (hz : 0 < ((sg : ℤ) : ℝ) * z.im) (α β : ℕ) :
    Integrable (phi1 sg t z ξ α β) := by
  have hB : (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z).re < 0 := by
    have hBeq : 2 * (Real.pi : ℂ) * I * ((sg : ℤ) : ℂ) * z = ((2 * Real.pi * ((sg : ℤ) : ℝ) : ℝ) : ℂ) * (I * z) := by
      push_cast
      ring
    rw [hBeq, Complex.re_ofReal_mul, Complex.I_mul_re]
    have := mul_pos Real.pi_pos hz
    nlinarith
  have h := PositivityTheory.SiegelWeilFormula.KLI.intg_poly2 hB (PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ) (PositivityTheory.SiegelWeilFormula.KLI.muF t ξ)
    (PositivityTheory.SiegelWeilFormula.KLI.Rab α β)
  rw [← (MeasurePreserving.symm Complex.measurableEquivRealProd Complex.volume_preserving_equiv_real_prod).integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [Function.comp_apply, PositivityTheory.SiegelWeilFormula.KLI.mer_symm,
    PositivityTheory.SiegelWeilFormula.KLI.gaussian_moment_real_coords]
end PositivityTheory.SiegelWeilFormula.KLI
