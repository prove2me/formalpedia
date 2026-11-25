-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin.ga_nn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:33.298594+00:00
-- url     : https://prove2.me/submissions/3b550a37-84df-4e8c-be36-e7acb0e0f546

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
theorem _root_.solution (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : 0 ≤ Ga k r l Y := by
  unfold Ga
  open scoped ComplexOrder in
  have key : ∀ {m : ℕ} (W : Fin m → Fin (2 * r + k + 1) → ℂ),
      0 ≤ (Matrix.of fun a b => star (W a) ⬝ᵥ W b).det.re := by
    intro m W
    have h : (Matrix.of fun a b => star (W a) ⬝ᵥ W b) =
        (Matrix.of fun i a => W a i)ᴴ * Matrix.of fun i a => W a i := by
      ext a b
      simp [Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply]
    rw [h]
    exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg).1
  exact key _
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
