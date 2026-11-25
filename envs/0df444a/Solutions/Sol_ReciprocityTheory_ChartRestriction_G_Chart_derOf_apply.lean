-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.derOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:06:02.200823+00:00
-- url     : https://prove2.me/submissions/a3cfe3f1-8259-4ca5-8104-ad10cabc5f80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_Lemmata_MiscLemmasQ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B]
variable {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
variable [Module B A] [IsScalarTower S B A] (hsm : ∀ (b : B) (a : A), b • a = e b * a)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (h : B →ₐ[S] DualNumber A) (hh : IsTanAt e h) (b : B) : derOf e hsm h hh b = (h b).snd := rfl
end ReciprocityTheory.ChartRestriction.G.Chart
