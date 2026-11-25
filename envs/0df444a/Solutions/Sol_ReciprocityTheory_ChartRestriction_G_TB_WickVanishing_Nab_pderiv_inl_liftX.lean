-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.pderiv_inl_liftX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:11.620082+00:00
-- url     : https://prove2.me/submissions/bf8f2702-ff81-44ad-a5ea-8441e8e588b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionKillsSeries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_subst


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (f : PS k 1 d) (j : Fin d) :
    pderiv k (Sum.inl j) (liftX k f) = liftX k (pderiv k ((0 : Fin 1), j) f) := by
  classical
  unfold liftX
  rw [LogPf.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _) f (Sum.inl j)]
  rw [Finset.sum_eq_single ((0 : Fin 1), j)]
  · simp [MvPowerSeries.pderiv_X]
  · intro p _ hp
    have hp' : p.2 ≠ j := by
      intro h
      exact hp (Prod.ext (Subsingleton.elim _ _) h)
    simp [MvPowerSeries.pderiv_X, Pi.single_apply, hp']
  · simp
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
