-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.integrable_mono0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:16.671555+00:00
-- url     : https://prove2.me/submissions/cc47283b-dac9-447d-9fca-7af7c60ff02b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integrable_mono
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_e_zero
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
theorem _root_.solution {b : ℝ} (hb : 0 < b) (s : ι →₀ ℕ) :
    Integrable (fun η : EuclideanSpace ℝ ι =>
      eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) := by
  have h := integrable_mono hb s 0
  simp_rw [e_zero] at h
  exact h
end PositivityTheory.SiegelWeilFormula.KFPB
