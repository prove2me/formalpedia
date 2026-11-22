-- Prove2me | solution 1 for P2M_Formalism_GM_tieE_apply__373a5b0b31bc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:56.380922+00:00
-- url     : https://prove2.me/submissions/4651e20d-aafe-4ccb-a1d6-c7617ba5d6a5

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM
theorem _root_.solution (g : MvPolynomial σ k) :
    tieE w e g = (∑ c, X (w c) * X (e c)) * g := by
  rfl
end Formalism.GM
