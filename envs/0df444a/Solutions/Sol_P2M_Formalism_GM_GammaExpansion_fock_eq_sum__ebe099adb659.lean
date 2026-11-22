-- Prove2me | solution 1 for P2M_Formalism_GM_GammaExpansion_fock_eq_sum__ebe099adb659
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:12.719454+00:00
-- url     : https://prove2.me/submissions/e43fa419-cd84-47a4-81c4-6435d646613c

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_eq_sum
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (hs : G.support ⊆ s) :
    M.fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * fw p m := by
  rw [fock_comm, fock_eq_sum p G F s hs]
  exact Finset.sum_congr rfl fun m _ => by ring
end Formalism.GM.GammaExpansion
