-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.jetAug_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:04.047888+00:00
-- url     : https://prove2.me/submissions/f06031d2-4237-4e4b-832c-69a5c5be7e16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SingleMemDegLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SubstTanSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
theorem _root_.solution {ι : Type} (q : MvPolynomial ι V) :
    jetAug (R := V) (m := 1) (Ideal.Quotient.mk _ q) = constantCoeff q := by
  show aeval (fun _ => (0 : V)) q = constantCoeff q
  exact RingHom.congr_fun MvPolynomial.eval_zero' q
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
