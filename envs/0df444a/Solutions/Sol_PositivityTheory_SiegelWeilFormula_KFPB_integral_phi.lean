-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.integral_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:12.996727+00:00
-- url     : https://prove2.me/submissions/0cb4c48a-cc76-4cd9-993b-a5ce97a09d43

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
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution {b : ℝ} (hb : 0 < b) (k : ℕ) (c : ℂ) :
    ∫ x, phi b k c x = (pk (-b : ℂ) k).eval c * (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * cexp (c ^ 2 / (4 * b))) := by
  have h : ((-b : ℂ)).re < 0 := by simp; linarith
  have e1 := J_eq h k c
  rw [J_zero h] at e1
  have e2 : ∫ x, phi b k c x = J (-b : ℂ) k c := rfl
  rw [e2, e1]
  congr 2
  · rw [neg_neg]
  · congr 1; ring
end PositivityTheory.SiegelWeilFormula.KFPB
