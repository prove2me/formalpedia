-- Prove2me | solution 1 for P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_divDer_zero__c709542f8f89
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:59.371807+00:00
-- url     : https://prove2.me/submissions/90bcf5eb-ffcb-4f23-8326-7d5517138d25

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_coeff_divDer

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
theorem _root_.solution (F : MvPolynomial (ι × Fin n) R) : divDer 0 F = F := by
  ext μ
  rw [coeff_divDer]
  simp
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
