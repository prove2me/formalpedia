-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.volume_coord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:55.050801+00:00
-- url     : https://prove2.me/submissions/c13a87a3-a7eb-4d11-a0c6-f84dbccabc47

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution {n : ℕ} (i : Fin n) : volume {y : Fin n → ℂ | y i = 0} = 0 := by
  have : {y : Fin n → ℂ | y i = 0} = Function.eval i ⁻¹' {0} := rfl
  rw [this, volume_pi]
  exact Measure.pi_eval_preimage_null _ (measure_singleton 0)
end ReciprocityTheory.AnForm.M.PLAux
