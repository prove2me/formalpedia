-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.ofLin_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:29.633354+00:00
-- url     : https://prove2.me/submissions/6d676b9b-55f9-4bb8-9eb4-458518b9f802

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
theorem _root_.solution (g : Ω[B⁄S] →ₗ[B] A) (b : B) : (ofLin e hsm g b).snd = g (KaehlerDifferential.D S B b) := by
  simp [ofLin]
end ReciprocityTheory.ChartRestriction.G.Chart
