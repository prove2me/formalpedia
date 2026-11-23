-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:57.604852+00:00
-- url     : https://prove2.me/submissions/ba64c980-7c58-42b9-bb73-af123d3c930a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain

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
open MvPowerSeries Formalism.FG.SolveVAux
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {σ τ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (u v : τ) (g : MvPowerSeries τ k) : pderiv k u (pderiv k v g) = pderiv k v (pderiv k u g) := by
  ext n
  simp only [MvPowerSeries.coeff_pderiv]
  by_cases huv : u = v
  · subst huv
    rfl
  · have h1 : (n + Finsupp.single u 1 : τ →₀ ℕ) v = n v := by simp [Finsupp.single_apply, huv]
    have h2 : (n + Finsupp.single v 1 : τ →₀ ℕ) u = n u := by simp [Finsupp.single_apply, Ne.symm huv]
    rw [h1, h2, add_right_comm n]
    ring
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
