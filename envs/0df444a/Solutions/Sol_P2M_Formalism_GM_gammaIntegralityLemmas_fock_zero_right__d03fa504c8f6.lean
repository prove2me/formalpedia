-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas_fock_zero_right__d03fa504c8f6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:38.546671+00:00
-- url     : https://prove2.me/submissions/68efd674-7d97-4820-b53d-761ab8e46afd

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution {σ : Type} [Fintype σ] [DecidableEq σ] (F : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p F 0 = 0 := by
  simp [Formalism.GM.M.fock]
end Formalism.GM.gammaIntegralityLemmas
