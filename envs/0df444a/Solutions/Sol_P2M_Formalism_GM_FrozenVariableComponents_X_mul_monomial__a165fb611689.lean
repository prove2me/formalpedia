-- Prove2me | solution 1 for P2M_Formalism_GM_FrozenVariableComponents_X_mul_monomial__a165fb611689
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:12.705849+00:00
-- url     : https://prove2.me/submissions/7ef12b38-a69f-4801-8840-bb633d89d8fe

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
theorem _root_.solution {σ : Type*} (x : σ) (m : σ →₀ ℕ) (a : K) :
    (X x : MvPolynomial σ K) * monomial m a = monomial (m + Finsupp.single x 1) a := by
  show monomial (Finsupp.single x 1) (1 : K) * monomial m a = _
  rw [monomial_mul, one_mul, add_comm]
end Formalism.GM.FrozenVariableComponents
