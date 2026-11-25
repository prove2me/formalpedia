-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_ga_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:07.01069+00:00
-- url     : https://prove2.me/submissions/9005e072-0e6a-4c03-a18b-17088a9c2831

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_StarLastDotLast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r : ℕ} (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1)) : 0 ≤ Ga k r l Y := by
  let A : Matrix (Fin (2 * r + k + 1)) (Fin (l.val + 1)) ℂ := Matrix.of fun i b => Y (Fin.castLE (by omega) b) i
  have e : Aᴴ * A = Matrix.of fun a b : Fin (l.val + 1) =>
      star (Y (Fin.castLE (by omega) a)) ⬝ᵥ Y (Fin.castLE (by omega) b) := by
    ext a b; simp [A, Matrix.mul_apply, dotProduct]
  have h := (posSemidef_conjTranspose_mul_self A).det_nonneg
  rw [e] at h
  exact (Complex.nonneg_iff.mp h).1
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
