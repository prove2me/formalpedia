-- Prove2me | solution 1 for P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_X_eq_monomial__aa92a785880b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:08.774766+00:00
-- url     : https://prove2.me/submissions/240e195b-c90f-4908-ada0-1b9e2b522a77

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
theorem _root_.solution (v : ι × Fin n) : (X v : MvPolynomial (ι × Fin n) R) = monomial (Finsupp.single v 1) 1 := rfl
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
