-- Prove2me | solution 1 for PositivityTheory.RgJS.NewtonIdentitiesAlt.card_filter_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:31.796309+00:00
-- url     : https://prove2.me/submissions/b58a4eae-4c6d-4690-887e-471c1ac69768

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLowerBounds_NewtonIdentitiesLowDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.NewtonIdentitiesAlt
variable {A : Type} [Fintype A]
omit [Fintype A]
namespace PositivityTheory.RgJS.NewtonIdentitiesAlt
theorem _root_.solution (j : ℕ) : #{x ∈ antidiagonal j | x.1 < j} ≤ j := by
  calc #{x ∈ antidiagonal j | x.1 < j} ≤ #(range j) :=
        Finset.card_le_card_of_injOn Prod.fst
          (fun x hx => by
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
            simp only [Finset.coe_range, Set.mem_Iio]
            exact hx.2)
          (fun x hx y hy hxy => by
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
            have e1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx.1
            have e2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hy.1
            exact Prod.ext hxy (by omega))
    _ = j := Finset.card_range j
end PositivityTheory.RgJS.NewtonIdentitiesAlt
