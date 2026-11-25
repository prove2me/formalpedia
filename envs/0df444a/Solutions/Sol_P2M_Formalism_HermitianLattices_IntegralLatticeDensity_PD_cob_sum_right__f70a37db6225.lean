-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_sum_right__f70a37db6225
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:31.017166+00:00
-- url     : https://prove2.me/submissions/475ebd88-361a-4f78-bf07-f401d030b6fe

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_add_right__9a421b50c142
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_right__b09b3a439bc2

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
    {J : Type} (a : M) (s : Finset J) (x : J → M) :
    cob φ a (∑ j ∈ s, x j) = ∑ j ∈ s, cob φ a (x j) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_right' h1]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, cob_add_right' h1, ih]
end Formalism.HermitianLattices.IntegralLatticeDensity.PD
