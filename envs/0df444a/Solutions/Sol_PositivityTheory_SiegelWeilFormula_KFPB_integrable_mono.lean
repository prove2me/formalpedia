-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.integrable_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:25.394432+00:00
-- url     : https://prove2.me/submissions/3d2c4426-564a-481e-a7b4-2f1519ca1c1b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integrable_euc
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integrable_phi
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_mono_prod
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
    Integrable (fun η : EuclideanSpace ℝ ι => 𝐞 (inner ℝ η u) •
      (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ))) := by
  refine integrable_euc ?_
  simp_rw [mono_prod]
  exact Integrable.fintype_prod (f := fun i y => phi b (s i) (2 * Real.pi * I * u i) y)
    fun i => integrable_phi hb _ _
end PositivityTheory.SiegelWeilFormula.KFPB
