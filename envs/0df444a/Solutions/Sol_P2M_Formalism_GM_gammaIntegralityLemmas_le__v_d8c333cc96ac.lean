-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas_le__v_d8c333cc96ac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:45.592842+00:00
-- url     : https://prove2.me/submissions/9bc0e72c-940d-495a-b5f2-6a18f13da017

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
theorem _root_.solution (β : Fin (N + 1 + 1) × Fin r →₀ ℕ) (i : Fin (N + 1 + 1)) (c : Fin r) : β (i, c) ≤ δv β i :=
  Finset.single_le_sum (f := fun c => β (i, c)) (fun _ _ => Nat.zero_le _) (mem_univ c)
end Formalism.GM.gammaIntegralityLemmas
