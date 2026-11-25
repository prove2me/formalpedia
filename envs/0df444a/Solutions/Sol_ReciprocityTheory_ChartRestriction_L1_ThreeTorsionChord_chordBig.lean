-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.ThreeTorsionChord.chordBig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:34:28.5728+00:00
-- url     : https://prove2.me/submissions/390fd4d1-c957-4cdd-b651-fbdd7fd75754

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_TorInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorsUnit3
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_dom
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sub_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F WeierstrassCurve
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open ReciprocityTheory.ChartRestriction.L1.ThreeTorsionChord
open Formalism.ELL.FormalGroupPointsTorsion
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1.ThreeTorsionChord
theorem _root_.solution {x y x2 y2 m : K} (h2 : ‖(2 : K)‖ = 1) (hx : ‖x‖ < 1) (hy : ‖y‖ = 1)
    (hx2 : ‖x2‖ < 1) (hy2 : ‖y2 + y‖ < 1) (hne : x2 ≠ x) (hm : m = (y2 - y) / (x2 - x)) :
    1 < ‖m ^ 2 - x2 - x‖ := by
  have hn : ‖y2 - y‖ = 1 := by
    have : y2 - y = -(2 * y) + (y2 + y) := by ring
    rw [this, dom (by rw [norm_neg, norm_mul, h2, hy, one_mul]; exact hy2), norm_neg, norm_mul,
      h2, hy, one_mul]
  have hd : ‖x2 - x‖ < 1 := sub_lt hx2 hx
  have hd0 : 0 < ‖x2 - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hm1 : 1 < ‖m‖ := by
    rw [hm, norm_div, hn]; exact (one_lt_div hd0).mpr hd
  have hmm : 1 < ‖m ^ 2‖ := by rw [norm_pow]; exact one_lt_pow₀ hm1 (by norm_num)
  have : m ^ 2 - x2 - x = m ^ 2 + (-x2 - x) := by ring
  rw [this, dom ((sub_lt (by rwa [norm_neg]) hx).trans hmm)]
  exact hmm
end ReciprocityTheory.ChartRestriction.L1.ThreeTorsionChord
