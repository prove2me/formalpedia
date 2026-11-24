-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.mono_spMap_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:12.095088+00:00
-- url     : https://prove2.me/submissions/84b13865-cd87-4e0d-a323-8f7b554599e9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {F : Type} [Field F] (V : ValuationSubring F) : Mono (spMap V.subtype) := by
  have h : Epi (CommRingCat.ofHom (algebraMap V F)) := IsLocalization.epi (nonZeroDivisors V) F
  show Mono (Spec.map (CommRingCat.ofHom (algebraMap V F)))
  exact Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap V F)).op
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
