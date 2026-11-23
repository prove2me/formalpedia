-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ordGE_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:17.789796+00:00
-- url     : https://prove2.me/submissions/bd0ae053-4c55-443b-ae4f-33c794524a7a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP

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
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]
namespace ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
theorem _root_.solution {σ : Type} {a b : ℕ} {f g : MvPowerSeries σ k} (hf : OrdGE a f) (hg : OrdGE b g) :
    OrdGE (a + b) (f * g) := by
  classical
  intro e he
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  replace hp : p.1 + p.2 = e := by
    first
    | exact Finset.mem_antidiagonal.mp hp
    | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    | simpa using hp
  have hd : p.1.degree + p.2.degree = e.degree := by
    rw [← hp]
    first
    | exact (map_add _ _ _).symm
    | simp
  by_cases h1 : p.1.degree < a
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
