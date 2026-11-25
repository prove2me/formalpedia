-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.cc_T_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:20.066797+00:00
-- url     : https://prove2.me/submissions/9f062341-5e7b-42ba-8570-e2a449621bb1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CcTMulQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_T_q_long
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_T_cons


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
theorem _root_.solution (b : List ι) : constantCoeff (T F u b q) = ev2 c b := by
  rcases b with _ | ⟨x, _ | ⟨y, _ | ⟨z, b⟩⟩⟩
  · exact hq0
  · rw [T_cons]
    exact hq1 x
  · rw [T_cons, T_cons]
    change constantCoeff (Dof F (u x) (Dof F (u y) q)) = c x y
    rw [hq2, constantCoeff_C]
  · rw [T_q_long c F u q hq2 _ (by simp), map_zero]
    rfl
end ReciprocityTheory.ChartRestriction.G.TB.G2
