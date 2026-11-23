-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_ev__53681771e208
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:35.649442+00:00
-- url     : https://prove2.me/submissions/89af2efb-4582-4156-a4e1-7a4b409a6be1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
variable {R k}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution {K : Type} [CommRing K] {m n d : ℕ} {a : Fin m → Pt K n d} (ha : CZ a) (f : PS K m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => ha p.1 p.2)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
          (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs'),
      smul_zero]
    rw [map_pow, ha s.1 s.2, zero_pow hs']
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
