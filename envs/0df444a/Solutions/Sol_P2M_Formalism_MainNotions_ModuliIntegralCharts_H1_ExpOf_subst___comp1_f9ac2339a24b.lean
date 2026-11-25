-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_subst___comp1_f9ac2339a24b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:29.611516+00:00
-- url     : https://prove2.me/submissions/de9211a6-3d7f-4fb1-8a3d-05b1f55a38fd

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_hasSubst___01ac09189af3
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
theorem _root_.solution (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (b : Fin 2) (i : Fin d) :
    subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2) (comp1 ε (pt S (n := 2) d b) i) =
      subst (fun q : Fin 1 × Fin d => linPt uvec b q.2) (ε i) := by
  have ha : HasSubst (fun q : Fin 1 × Fin d => (![pt S (n := 2) d b] : Fin 1 → Pt S 2 d) q.1 q.2) :=
    hasSubst_of_constantCoeff_zero fun q => by
      obtain ⟨k, i⟩ := q
      fin_cases k
      simp [pt]
  rw [comp1, ev, subst_comp_subst_apply ha (hasSubst_Λ uvec)]
  congr 1
  funext q
  obtain ⟨k, i'⟩ := q
  fin_cases k
  show subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2) (X (b, i')) = _
  rw [subst_X (hasSubst_Λ uvec)]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
