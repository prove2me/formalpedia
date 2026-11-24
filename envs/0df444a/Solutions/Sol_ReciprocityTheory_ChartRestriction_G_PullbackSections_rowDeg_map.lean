-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.rowDeg_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:58.142671+00:00
-- url     : https://prove2.me/submissions/ceb151d3-0562-4d48-b7bd-158f5f9975e4

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Mathlib.Algebra.MvPolynomial.Funext
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_FFVMap

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open NumberField IsDedekindDomain Formalism.L2.Pj MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k K : Type} [Field k] [Field K]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (io : k →+* K) {a : Ty → ℕ → ℕ} {P : MvPolynomial (Letter Ty r n) k} (hP : RowDeg r n k a P) :
    RowDeg r n K a (P.map io) := by
  intro m hm
  rw [support_map_of_injective _ io.injective] at hm
  exact hP m hm
end ReciprocityTheory.ChartRestriction.G.PullbackSections
