-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_add_right__9a421b50c142
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:19.175373+00:00
-- url     : https://prove2.me/submissions/85f3e097-33e6-4ae9-8058-bb7bc2d41fb4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_symm__15ad48273a45

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity Formalism.HermitianLattices.IntegralLatticeDensity.PD
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
variable {M Q : Type} [AddCommGroup M] [AddCommGroup Q] {φ : M → Q}
namespace Formalism.HermitianLattices.IntegralLatticeDensity.PD
theorem _root_.solution (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a b b' : M) :
    cob φ a (b + b') = cob φ a b + cob φ a b' := by
  rw [cob_symm', h1, cob_symm' b, cob_symm' b']
end Formalism.HermitianLattices.IntegralLatticeDensity.PD
