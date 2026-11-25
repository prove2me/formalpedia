-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.om_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:44.952795+00:00
-- url     : https://prove2.me/submissions/e418e896-de94-415b-85e1-fae24bb5baf4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_om_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_mul_om
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_map_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_map_ev_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_jac_F


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (i b : Fin d) : ∑ j, ev (n := 2) ![G.F] (Om G i j) * Ar G j b = ev (n := 2) ![pt k d 1] (Om G i b) := by
  have hF : CZ (![G.F] : Fin 1 → Pt k 2 d) := by
    intro j i
    fin_cases j
    simpa using G.const i
  have hY : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := by
    intro j i
    fin_cases j
    simp [pt]
  have hJ : (JM G).map (ev (n := 2) ![G.F]) = Matrix.of (Ar G) * (JM G).map (ev (n := 2) ![pt k d 1]) := by
    refine Matrix.ext fun i b => ?_
    rw [Matrix.mul_apply]
    exact jac_F G i b
  have h1 : (Om G).map (ev (n := 2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) = 1 := by
    rw [← map_ev_mul hF, om_mul, map_ev_one hF]
  have h2 : (JM G).map (ev (n := 2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1]) = 1 := by
    rw [← map_ev_mul hY, mul_om, map_ev_one hY]
  have h3 : (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G) = (Om G).map (ev (n := 2) ![pt k d 1]) := by
    calc (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G)
        = (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G) *
            ((JM G).map (ev (n := 2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1])) := by
          rw [h2, Matrix.mul_one]
      _ = (Om G).map (ev (n := 2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) *
            (Om G).map (ev (n := 2) ![pt k d 1]) := by
          rw [hJ]
          simp only [Matrix.mul_assoc]
      _ = (Om G).map (ev (n := 2) ![pt k d 1]) := by
          rw [h1, Matrix.one_mul]
  have h4 := congrFun (congrFun h3 i) b
  rw [Matrix.mul_apply] at h4
  first
    | exact h4
    | simpa using h4
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
