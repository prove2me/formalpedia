-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ChartPrimTrPf_prim__comm_976fe62e9077
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:13.555147+00:00
-- url     : https://prove2.me/submissions/0a1b12c1-5945-4d75-83fb-8f41e5670b0e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartFrameTrA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
theorem _root_.solution {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) : primφ t' k ≫ m.φ = m.φ ≫ primφ t k := by
  rcases k with k | I
  · simp [primφ]
  · show (psum t'.G ![𝟙 t'.G, t'.act.act H.w0] I.down).left ≫ m.cm.F =
      m.cm.F ≫ (psum t.G ![𝟙 t.G, t.act.act H.w0] I.down).left
    refine (psum_push m.cart ![𝟙 t'.G, t'.act.act H.w0] ![𝟙 t.G, t.act.act H.w0] (pushPt m.cart.1.w (𝟙 t'.G))
      (fun i => ?_) I.down).trans ?_
    · fin_cases i
      · simp
      · exact Over.OverMorphism.ext (by simp [pushPt, m.act H.w0])
    · simp [pushPt]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
