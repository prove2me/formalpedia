-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.nabVal_eq_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:05.420264+00:00
-- url     : https://prove2.me/submissions/53bbc47b-f0e9-4c88-8f55-c8e4bbc9762b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull

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
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (k : Type)
    [CommRing k] [Algebra ℚ k] [Algebra R k] [Nontrivial k] (B : FB R d O) (h : PS k 2 d) (w0 : O) (m : ℕ)
    (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k) (Q : MvPolynomial ι k) :
    B.nabVal k h w0 m f u Q = lam (fun e => B.nabVal k h w0 m f u (monomial e 1)) Q := by
  classical
  unfold FB.nabVal lam
  simp only [DpolyOf, map_sum, map_mul, MvPowerSeries.constantCoeff_C]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  simp [MvPolynomial.support_monomial, MvPolynomial.coeff_monomial]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
