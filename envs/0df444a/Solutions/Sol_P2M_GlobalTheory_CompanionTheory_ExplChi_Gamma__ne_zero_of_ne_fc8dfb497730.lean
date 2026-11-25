-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_ExplChi_Gamma__ne_zero_of_ne_fc8dfb497730
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:24.960316+00:00
-- url     : https://prove2.me/submissions/701f89d1-85d5-469d-bc57-2e6480574008

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivReflectionFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplChi
open Complex DirichletCharacter
namespace GlobalTheory.CompanionTheory.ExplChi
theorem _root_.solution {z : ℂ} (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) : Gammaℝ z ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Gammaℝ_def]
  exact mul_ne_zero (by rw [Ne, cpow_eq_zero_iff]; exact fun h => hpi h.1) (Gamma_ne_zero hz)
end GlobalTheory.CompanionTheory.ExplChi
