-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.herm_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:47:00.993581+00:00
-- url     : https://prove2.me/submissions/9f2663af-9204-400d-9e73-744c2c170b14

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution (r c : Fin n) : herm (v1 r c) + Complex.I • herm (v2 r c) = Matrix.single r c 1 := by
  ext i j
  have e1 : (if j = r ∧ i = c then (1:ℝ) else 0) = if i = c ∧ j = r then 1 else 0 := by
    simp only [and_comm]
  have e2 : (if j = c ∧ i = r then (1:ℝ) else 0) = if i = r ∧ j = c then 1 else 0 := by
    simp only [and_comm]
  have e3 : (Matrix.single r c (1:ℂ)) i j = (((if i = r ∧ j = c then (1:ℝ) else 0 : ℝ)) : ℂ) := by
    rw [Matrix.single_apply]
    by_cases h : i = r ∧ j = c
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]; simp
  rw [e3]
  simp only [herm, v1, v2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e1, e2]
  generalize (if i = r ∧ j = c then (1:ℝ) else 0) = a
  generalize (if i = c ∧ j = r then (1:ℝ) else 0) = b
  push_cast
  linear_combination ((b:ℂ) - a) / 2 * Complex.I_sq
end PositivityTheory.Rg.Sw.LVs.STD
