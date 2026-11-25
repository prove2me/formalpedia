-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.pderiv_eval_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:40.218751+00:00
-- url     : https://prove2.me/submissions/18634d79-39bc-40a1-b78f-2dff0d6e4422

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_pd_sb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution {j : Fin n} {u v w : Q k d n} {s t r : PS k n d} (hu : Dir j u s) (hv : Dir j v t) (hw : Dir j w r) (b : Fin d)
    (f : PS k 3 d) : pderiv k (j, b) (E3 f u v w) =
      E3 (pderiv k (0, b) f) u v w * s + E3 (pderiv k (1, b) f) u v w * t + E3 (pderiv k (2, b) f) u v w * r := by
  have hd : ∀ i, Dir j (![u, v, w] i) (![s, t, r] i) := fun i => by
    fin_cases i
    · exact hu
    · exact hv
    · exact hw
  show pderiv k (j, b) (sb ![u, v, w] f) = _
  rw [pd_sb ![u, v, w] ![s, t, r] hd b f, Fin.sum_univ_three]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.G.TB.Canon
