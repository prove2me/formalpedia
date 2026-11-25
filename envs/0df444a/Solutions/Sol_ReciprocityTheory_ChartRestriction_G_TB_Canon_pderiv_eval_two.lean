-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.pderiv_eval_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:44.102903+00:00
-- url     : https://prove2.me/submissions/2921ec46-dd6a-4380-a7f9-92bde3350724

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
theorem _root_.solution {j : Fin n} {u v : Q k d n} {s t : PS k n d} (hu : Dir j u s) (hv : Dir j v t) (b : Fin d) (f : PS k 2 d) :
    pderiv k (j, b) (E2 f u v) = E2 (pderiv k (0, b) f) u v * s + E2 (pderiv k (1, b) f) u v * t := by
  have hd : ∀ i, Dir j (![u, v] i) (![s, t] i) := fun i => by
    fin_cases i
    · exact hu
    · exact hv
  show pderiv k (j, b) (sb ![u, v] f) = _
  rw [pd_sb ![u, v] ![s, t] hd b f, Fin.sum_univ_two]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.G.TB.Canon
