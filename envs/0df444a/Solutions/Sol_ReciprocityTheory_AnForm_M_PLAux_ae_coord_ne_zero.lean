-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.ae_coord_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:20.656649+00:00
-- url     : https://prove2.me/submissions/693a92ac-ccc2-4812-962d-d57d138b6043

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_volume_coord_eq_zero

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
theorem _root_.solution {n : ℕ} : ∀ᵐ y : Fin n → ℂ, ∀ i, y i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  simpa using volume_coord_eq_zero i
end ReciprocityTheory.AnForm.M.PLAux
