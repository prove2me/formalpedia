-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_symm__15ad48273a45
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:47.817721+00:00
-- url     : https://prove2.me/submissions/a4b5205c-6017-46c9-91db-0c5ec19f389c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit

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
theorem _root_.solution (a b : M) : cob φ a b = cob φ b a := by
  simp only [cob]
  rw [add_comm a b]
  abel
end Formalism.HermitianLattices.IntegralLatticeDensity.PD
