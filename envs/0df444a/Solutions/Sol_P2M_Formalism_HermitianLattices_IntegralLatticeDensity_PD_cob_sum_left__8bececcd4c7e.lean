-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_left__8bececcd4c7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:21.670814+00:00
-- url     : https://prove2.me/submissions/46e17e87-031d-4469-8dc3-3de555da9241

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_left__fffdab6f3c0e

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
theorem _root_.solution (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (b : M) (s : Finset J) (x : J → M) :
    cob φ (∑ j ∈ s, x j) b = ∑ j ∈ s, cob φ (x j) b := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_left' h1]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, h1, ih]
end Formalism.HermitianLattices.IntegralLatticeDensity.PD
