-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_ColumnFamilies_qn_full__25b017f46351
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:20.338649+00:00
-- url     : https://prove2.me/submissions/9d7c00cf-e17f-40d9-b8a1-73e0dfa817ff

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_full

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) (h : s = n) :
    ∃ ε : ℤ, initMinor ℤ J hs = ε • qn_delta n := by
  subst h
  exact qn_full s J
end Formalism.InvariantFactorPaths.ColumnFamilies
