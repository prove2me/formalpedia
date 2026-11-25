-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.jetTan_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:56:02.019265+00:00
-- url     : https://prove2.me/submissions/c0729c71-5fe5-46d2-b130-d045322092fb

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
theorem _root_.solution {ι : Type} [DecidableEq ι] (ℓ : ι) (q : MvPolynomial ι V) :
    jetTan (R := V) (m := 0) ℓ (Ideal.Quotient.mk _ q) =
      aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber V) else 0) q := rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
