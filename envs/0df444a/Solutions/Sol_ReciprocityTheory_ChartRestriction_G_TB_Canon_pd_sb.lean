-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.pd_sb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:54:13.167505+00:00
-- url     : https://prove2.me/submissions/c74ca3e5-d1eb-445c-bf71-c2cfcefaf045

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev


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
theorem _root_.solution {m : ℕ} (a : Fin m → Q k d n) (t : Fin m → PS k n d) {j : Fin n} (h : ∀ i, Dir j (a i) (t i)) (b : Fin d)
    (f : PS k m d) : pderiv k (j, b) (sb a f) = ∑ i, sb a (pderiv k (i, b) f) * t i := by
  rw [sb_apply, pderiv_ev (czQ a), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [h i b, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, sb_apply]
end ReciprocityTheory.ChartRestriction.G.TB.Canon
