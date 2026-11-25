-- Prove2me | solution 1 for P2M_Formalism_GM_FrozenVariableComponents_X_pow_mul_monomial__30fbf852bce7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:03.385551+00:00
-- url     : https://prove2.me/submissions/165e4e89-0cb6-4c01-bded-b1e25d0b354a

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
variable {K : Type*} [CommRing K] {N r : ℕ}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution {σ : Type*} (x : σ) (k : ℕ) (m : σ →₀ ℕ) (a : K) :
    (X x : MvPolynomial σ K) ^ k * monomial m a = monomial (m + Finsupp.single x k) a := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul, add_comm]
end Formalism.GM.FrozenVariableComponents
