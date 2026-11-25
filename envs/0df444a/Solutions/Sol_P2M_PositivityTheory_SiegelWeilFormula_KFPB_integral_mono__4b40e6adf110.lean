-- Prove2me | solution 1 for P2M_PositivityTheory_SiegelWeilFormula_KFPB_integral_mono__4b40e6adf110
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:57.465134+00:00
-- url     : https://prove2.me/submissions/e0520f06-da55-4a8c-8df7-dfc668522fa9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integral_mono
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_prod_gauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_eval_rS
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
theorem _root_.solution {b : ℝ} (hb : 0 < b) (s : ι →₀ ℕ) (u : EuclideanSpace ℝ ι) :
    ∫ η : EuclideanSpace ℝ ι, 𝐞 (inner ℝ η u) •
      (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) =
      eval (fun i => ((u i : ℝ) : ℂ)) (rS b s) * (Real.exp (-(Real.pi ^ 2 / b * ‖u‖ ^ 2)) : ℂ) := by
  rw [integral_mono hb, prod_gauss hb, eval_rS]
  ring
end PositivityTheory.SiegelWeilFormula.KFPB
