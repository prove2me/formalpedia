-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas_pderiv_comm__40dd41c8beb1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:15.093157+00:00
-- url     : https://prove2.me/submissions/c90a7068-e6dc-4ea6-98d2-f573e6c12d7d

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (i j : σ) (q : MvPolynomial σ ℚ_[p]) :
    pderiv i (pderiv j q) = pderiv j (pderiv i q) := by
  ext m
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  by_cases h : i = j
  · subst h; rfl
  · have h1 : ((m + Finsupp.single i 1 : σ →₀ ℕ) : σ → ℕ) j = m j := by simp [Finsupp.single_apply, h]
    have h2 : ((m + Finsupp.single j 1 : σ →₀ ℕ) : σ → ℕ) i = m i := by simp [Finsupp.single_apply, Ne.symm h]
    rw [h1, h2, show m + Finsupp.single i 1 + Finsupp.single j 1 = m + Finsupp.single j 1 + Finsupp.single i 1 by
      rw [add_assoc, add_comm (Finsupp.single i 1), ← add_assoc]]
    ring
end Formalism.GM.gammaIntegralityLemmas
