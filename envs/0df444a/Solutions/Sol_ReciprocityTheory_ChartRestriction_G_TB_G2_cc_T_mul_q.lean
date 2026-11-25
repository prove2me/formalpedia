-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.cc_T_mul_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:56:11.731802+00:00
-- url     : https://prove2.me/submissions/071a416e-7542-4b17-ab89-aac84a1ff862

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CcTMulQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_cc_T_q
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_T_mul


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
variable {ι : Type} (c : ι → ι → k)
variable (F : Fin d → PS k 2 d) (u : ι → Fin d → k) (q : PS k 1 d)
  (hq0 : constantCoeff q = 0) (hq1 : ∀ l, constantCoeff (Dof F (u l) q) = 0)
  (hq2 : ∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l'))
include hq2
include hq0 hq1
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (w : List ι) (A : PS k 1 d) :
    constantCoeff (T F u w (A * q)) =
      ((splits w).map (fun p => constantCoeff (T F u p.1 A) * ev2 c p.2)).sum := by
  rw [T_mul, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, map_mul]
  rw [cc_T_q c F u q hq0 hq1 hq2]
end ReciprocityTheory.ChartRestriction.G.TB.G2
