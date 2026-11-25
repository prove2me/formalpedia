-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_T0_optionEquivLeft_rename_some__c92b016ed5b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:52:55.39261+00:00
-- url     : https://prove2.me/submissions/7c8f565b-661c-4605-a193-8097247b01de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentScaledForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {R S : Type*} [CommRing R] (a : MvPolynomial S R) :
    MvPolynomial.optionEquivLeft R S (MvPolynomial.rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on
  next r => simp [MvPolynomial.optionEquivLeft_C]
  next p q hp hq => simp [hp, hq]
  next p s hp => simp [hp, MvPolynomial.optionEquivLeft_X_some]
end ReciprocityTheory.ChartRestriction.G.T0
