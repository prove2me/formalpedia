-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:30.548644+00:00
-- url     : https://prove2.me/submissions/44fb8df2-76f3-4d25-a7ee-e86246b4aedc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (j i : Fin d) : (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1).degree = 2 := by
  have hadd : ∀ a b : Fin 2 × Fin d →₀ ℕ, (a + b).degree = a.degree + b.degree := by
    intro a b
    first
      | exact map_add _ a b
      | simp [Finsupp.degree_eq_weight_one, map_add]
      | simp [Finsupp.degree, Finsupp.sum_add_index']
  have hsg : ∀ x : Fin 2 × Fin d, (single x 1).degree = 1 := by
    intro x
    first
      | exact Finsupp.degree_single x 1
      | simp [Finsupp.degree_eq_weight_one]
      | simp [Finsupp.degree]
  rw [hadd, hsg, hsg]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
