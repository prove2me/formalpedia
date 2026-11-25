-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.integral_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:52.071042+00:00
-- url     : https://prove2.me/submissions/061eeaf3-346d-4a95-8ea6-f662a6da14e5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integral_euc
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integral_phi
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
    ∫ η : EuclideanSpace ℝ ι, 𝐞 (inner ℝ η u) •
      (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) =
      ∏ i, ((pk (-b : ℂ) (s i)).eval (2 * Real.pi * I * u i) *
        (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * cexp ((2 * Real.pi * I * u i) ^ 2 / (4 * b)))) := by
  rw [integral_euc]
  simp_rw [mono_prod]
  rw [integral_fintype_prod_volume_eq_prod (f := fun i y => phi b (s i) (2 * Real.pi * I * u i) y)]
  simp_rw [integral_phi hb]
end PositivityTheory.SiegelWeilFormula.KFPB
