-- Prove2me | solution 1 for P2M_GlobalTheory_FrameAdjSeries_wl_pt__be8a4af557c6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:57.726795+00:00
-- url     : https://prove2.me/submissions/02debe03-3a6e-48c3-b933-6cb19aa4de84

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjointnessSeriesOfFrames

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory GlobalTheory.FrameAdjSeries
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
namespace GlobalTheory.FrameAdjSeries
theorem _root_.solution {T : Over X0} (a b : T ⟶ t.G) (c : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift a b).left ≫ cφG t ![fst t.G t.G ≫ t.act.act c, snd t.G t.G] I =
      (psum t.G ![a ≫ t.act.act c, b] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a b ≫ (fst t.G t.G ≫ t.act.act c) = a ≫ t.act.act c
    exact lift_fst_assoc _ _ _
  · show lift a b ≫ snd t.G t.G = b
    exact lift_snd _ _
end GlobalTheory.FrameAdjSeries
