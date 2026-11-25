-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.degLt_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:15.928349+00:00
-- url     : https://prove2.me/submissions/d88185ad-713b-47a2-b488-487bc74e2582

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution {n : ℕ} {P : MvPolynomial ι k} (h : DegLt (n + 1) P) (l : ι) :
    DegLt n (MvPolynomial.pderiv l P) := by
  classical
  intro m hm
  rw [MvPolynomial.as_sum P, map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial]
  by_cases hsm : s - Finsupp.single l 1 = m
  · rw [if_pos hsm]
    have hc : MvPolynomial.coeff s P ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    rcases Nat.eq_zero_or_pos (s l) with h0 | hpos
    · simp [h0]
    · exfalso
      have hle : Finsupp.single l 1 ≤ s := by
        first
        | (rw [Finsupp.single_le_iff]; exact hpos)
        | exact Finsupp.single_le_iff.mpr hpos
      have hs' : m + Finsupp.single l 1 = s := by
        rw [← hsm]
        exact tsub_add_cancel_of_le hle
      have hdeg : s.degree = m.degree + 1 := by
        first
        | rw [← hs', Finsupp.degree_add, Finsupp.degree_single]
        | rw [← hs', map_add, Finsupp.degree_single]
        | (rw [← hs']; simp [Finsupp.degree_add])
        | (rw [← hs']; simp)
      exact hc (h s (by omega))
  · rw [if_neg hsm]
end ReciprocityTheory.ChartRestriction.G.TB.GE
