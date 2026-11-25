-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:20.250091+00:00
-- url     : https://prove2.me/submissions/e6794074-0a62-4abf-be3b-99adab72c1fd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Nat
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution (E : ℂ → ℂ) (hE : Differentiable ℂ E) (c : ℂ) (j : ℕ) :
    iteratedDeriv j (fun z => E (c * z)) 0 = c ^ j * iteratedDeriv j E 0 := by
  rw [iteratedDeriv_comp_const_mul hE.contDiff c]
  simp only [mul_zero]
end PositivityTheory.SiegelWeilFormula.KFPB
