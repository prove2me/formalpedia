-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_unit__map_07e5cd7c94ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:06.536806+00:00
-- url     : https://prove2.me/submissions/053c255e-cecf-457c-91da-31f7433bc5d6

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] {S : Type} [CommRing S] [Algebra S A] [Algebra S B]
    (σ : A →ₐ[S] B) (U : Aˣ) :
    unitΓ (Units.map (σ : A →* B) U) = pullU (spMap (σ : A →+* B)) ⊤ (unitΓ U) := by
  unfold unitΓ pullU
  ext
  simp [toΓ, spMap]
  have h2 := congrArg (fun g => CommRingCat.Hom.hom g (U : A))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : A →+* B)))
  exact h2
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
