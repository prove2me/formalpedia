-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.ratHom_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:29.039094+00:00
-- url     : https://prove2.me/submissions/d5626ddb-22fc-40d0-ad03-4c5f213fe9f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (P : Ideal (MvPolynomial σ ℤ)) (f : MvPolynomial σ ℤ) :
    ratHom P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk (qIdeal P) (qmap f) := rfl
end ReciprocityTheory.ChartRestriction.G.Geo
