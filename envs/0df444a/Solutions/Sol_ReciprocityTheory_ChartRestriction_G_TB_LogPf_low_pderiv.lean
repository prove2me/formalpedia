-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.low_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:07.10258+00:00
-- url     : https://prove2.me/submissions/7cc39b20-725f-4b80-896d-80f2b5c1db12

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
theorem _root_.solution {N : ℕ} {g : MvPowerSeries τ k} (hg : Low (N + 1) g) (t : τ) : Low N (pderiv k t g) := by
  intro d hd
  rw [MvPowerSeries.coeff_pderiv, hg, zero_mul]
  have e : Finsupp.degree (d + Finsupp.single t 1) = Finsupp.degree d + 1 := by
    first
    | rw [map_add, Finsupp.degree_single]
    | simp [Finsupp.degree, Finsupp.sum_add_index']
    | (unfold Finsupp.degree; rw [Finsupp.sum_add_index' (by simp) (by simp)]; simp)
  omega
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
