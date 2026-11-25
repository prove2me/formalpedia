-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.half_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:27.680054+00:00
-- url     : https://prove2.me/submissions/87d3a149-72ac-4184-b7ff-1aaf091e29f4

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
variable [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (hH : HalfSt) (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (c : ι → ι → k) (q : PS k 1 d) (hc : ∀ l l', c l l' = c l' l) (hq0 : constantCoeff q = 0)
    (hq1 : ∀ l, constantCoeff (Dof F (u l) q) = 0)
    (hq2 : ∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l')) (n : ℕ) :
    ∀ (P : MvPolynomial ι k) (A : PS k 1 d),
      constantCoeff (DpolyOf F u P (A * q ^ n)) =
        algebraMap ℚ k (1 / 2) ^ n * constantCoeff (DpolyOf F u ((secondOrder k c)^[n] P) A) := by
  induction n with
  | zero => intro P A; simp
  | succ n ih =>
    intro P A
    have e : A * q ^ (n + 1) = (A * q) * q ^ n := by ring
    rw [e, ih P (A * q), hH k d F ι u c q hc hq0 hq1 hq2 ((secondOrder k c)^[n] P) A,
      Function.iterate_succ_apply', pow_succ]
    ring
end ReciprocityTheory.ChartRestriction.G.TB.GE
