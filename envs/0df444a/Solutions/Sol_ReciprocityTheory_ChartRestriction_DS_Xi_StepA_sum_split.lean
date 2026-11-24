-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:33:21.984783+00:00
-- url     : https://prove2.me/submissions/189c824d-0c26-4f03-9f9a-b809807824f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (f : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ p, f p = f 0 + ∑ j, f (mp k r' j) + f ⟨2 * (1 + r') + k, by omega⟩ := by
  have h : 2 * r' + k + 1 + 1 = 2 * (1 + r') + k := by ring
  rw [Fin.sum_univ_succ, ← Fin.sum_congr' _ h, Fin.sum_univ_castSucc, add_assoc (f 0)]
  have e1 : ∀ j : Fin (2 * r' + k + 1), (Fin.cast h j.castSucc).succ = mp k r' j :=
    fun j => Fin.ext (by simp [mp])
  have e2 : (Fin.cast h (Fin.last (2 * r' + k + 1))).succ = ⟨2 * (1 + r') + k, by omega⟩ :=
    Fin.ext (by simp only [Fin.val_succ, Fin.coe_cast, Fin.val_last]; omega)
  simp only [e1, e2]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
