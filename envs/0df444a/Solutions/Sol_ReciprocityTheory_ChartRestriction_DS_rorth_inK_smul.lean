-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_inK_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:30.076838+00:00
-- url     : https://prove2.me/submissions/cc2e7b04-3797-439e-ac15-f79449cc5bd1

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
theorem _root_.solution {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (t : ℝ) :
    inK ε ((t : ℂ) • Z) := by
  obtain ⟨h1, h2⟩ := hZ
  refine ⟨?_, by rw [Matrix.smul_mul, Matrix.mul_smul, h2]⟩
  unfold inG at h1 ⊢
  have hs : star (t : ℂ) = t := Complex.conj_ofReal t
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
end ReciprocityTheory.ChartRestriction.DS
