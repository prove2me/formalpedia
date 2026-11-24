-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.mat_eq_of_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:59:56.971502+00:00
-- url     : https://prove2.me/submissions/52fe2a7a-aa25-4a0f-b166-b1bace1dfb65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution [DecidableEq ι] {A B : Matrix ι ι ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
