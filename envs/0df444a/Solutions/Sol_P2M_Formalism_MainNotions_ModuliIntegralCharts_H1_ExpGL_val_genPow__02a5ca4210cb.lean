-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_val_genPow__02a5ca4210cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:26.09313+00:00
-- url     : https://prove2.me/submissions/23282825-e96f-4e54-99dd-824c9993dd8a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpSActPS
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BqOriginSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocChart
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_val_genPowG


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL
theorem _root_.solution {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (k : ℕ) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) : val (genPow φ ε g k) r z J = val g r z J ^ k := by
  first
  | exact GermD.val_genPowG Xo.univ.t φ ε g k r z J
  | exact GermD.val_genPowG (t := Xo.univ.t) φ ε g k r z J
  | (simp only [genPow]; exact GermD.val_genPowG _ φ ε g k r z J)
  | (unfold genPow; exact GermD.val_genPowG _ φ ε g k r z J)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL
