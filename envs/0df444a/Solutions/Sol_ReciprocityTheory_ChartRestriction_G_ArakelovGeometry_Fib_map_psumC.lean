-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.map_psumC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:09.92264+00:00
-- url     : https://prove2.me/submissions/28084b0f-dbf8-4840-9df9-7ff9e0594fed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : Polynomial R)
    (n k : ℕ) : φ (psumC p n k) = psumC (p.map φ) n k := by
  unfold psumC
  induction psumQ n k using MvPolynomial.induction_on
  next a => simp
  next P1 P2 h1 h2 => simp only [map_add, h1, h2]
  next P1 i h1 => simp [h1, Polynomial.coeff_map]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
