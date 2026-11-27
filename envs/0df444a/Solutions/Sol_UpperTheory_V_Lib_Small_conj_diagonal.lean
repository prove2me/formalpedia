-- Prove2me | solution 1 for UpperTheory.V.Lib.Small.conj_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:17.052273+00:00
-- url     : https://prove2.me/submissions/28a32844-fb51-4456-b911-d0594c858d9a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtraAlt
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqOneOfNear
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtraBis
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MirabolicColumnBlock
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FinitelyGeneratedModPow
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_IntegralityNearIdentity_EqOneOfNear
import Theorems.Thm_UpperTheory_Reformulated_B_MirabolicColumnBlock_conj_diagonal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.V UpperTheory.V.Lib UpperTheory.V.Lib.Small
namespace UpperTheory.V.Lib.Small
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.charpoly = ∏ a, (Polynomial.X - Polynomial.C (d a))) :
    ∃ h : GL (Fin n) K, ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * h = Matrix.diagonal d :=
  _root_.UpperTheory.Reformulated.B.MirabolicColumnBlock.conj_diagonal d hd M hM
end UpperTheory.V.Lib.Small
