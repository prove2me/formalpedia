-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_single_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:39.594651+00:00
-- url     : https://prove2.me/submissions/1a2a4446-63f5-475f-bee8-c51ee7156924

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b (1 : ℂ) := by
  ext i j
  unfold Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases hij : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hij
    simp [h]
  · simp [hij]
end ReciprocityTheory.ChartRestriction.DS
