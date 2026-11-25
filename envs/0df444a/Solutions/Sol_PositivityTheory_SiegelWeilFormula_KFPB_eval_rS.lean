-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.eval_rS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:18.454973+00:00
-- url     : https://prove2.me/submissions/60234142-b53f-4717-b7e9-854387d46d4a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_eval_linP
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
theorem _root_.solution (b : ℝ) (s : ι →₀ ℕ) (u : EuclideanSpace ℝ ι) :
    eval (fun i => ((u i : ℝ) : ℂ)) (rS b s) =
      kG b ^ Fintype.card ι * ∏ i, (pk (-b : ℂ) (s i)).eval (2 * Real.pi * I * u i) := by
  simp [rS, eval_linP]
end PositivityTheory.SiegelWeilFormula.KFPB
