-- Prove2me | solution 1 for UpperTheory.V.Lib.Small.conj_of_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:21.554469+00:00
-- url     : https://prove2.me/submissions/52a078a6-92eb-439c-b94d-62418e76182e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_IntegralityNearIdentity_EqOneOfNear
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjugateOfRoots
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WeightedSumBis
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_IntegralityNearIdentity_ExistsContDiffEventuallyEq
import Theorems.Thm_UpperTheory_Reformulated_B_ConjugateOfRoots_conj_of_roots


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open UpperTheory UpperTheory.V UpperTheory.V.Lib UpperTheory.V.Lib.Small
namespace UpperTheory.V.Lib.Small
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d) (N D : GL (Fin n) K)
    (hD : (D : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hN : ∀ i, (N : Matrix (Fin n) (Fin n) K).charpoly.IsRoot (d i)) : ∃ g : GL (Fin n) K, N = g * D * g⁻¹ :=
  _root_.UpperTheory.Reformulated.B.ConjugateOfRoots.conj_of_roots d hd N D hD hN
end UpperTheory.V.Lib.Small
