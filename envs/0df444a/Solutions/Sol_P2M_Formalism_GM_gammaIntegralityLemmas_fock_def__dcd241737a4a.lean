-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas_fock_def__dcd241737a4a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:16.798946+00:00
-- url     : https://prove2.me/submissions/40099003-1598-414c-97f4-5bd046b06f3b

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_prod_eq_wf

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
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (F G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p F G = ∑ m ∈ F.support, F.coeff m * G.coeff m * wf m := by
  unfold Formalism.GM.M.fock
  exact Finset.sum_congr rfl (fun m _ => by rw [prod_eq_wf])
end Formalism.GM.gammaIntegralityLemmas
