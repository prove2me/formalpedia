-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.constSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:12.693188+00:00
-- url     : https://prove2.me/submissions/adfcc84d-30df-424c-b52d-98f9f0ad43e6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution : ConstSt := by
  intro k _ d φ hφ g
  have ha : ∀ p : Fin 1 × Fin d, constantCoeff (![φ] p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    simpa using hφ j
  have hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => ![φ] p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    have h0 : constantCoeff (e.prod fun s n => (![φ] s.1 s.2) ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
      rw [map_pow, ha p, zero_pow hp]
    rw [h0, smul_zero]
end ReciprocityTheory.ChartRestriction.G.TB
