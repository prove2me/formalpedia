-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:18.39269+00:00
-- url     : https://prove2.me/submissions/e4cbd748-fef9-4e42-8004-d5c8ef815e76

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
variable (k r : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [conjTranspose_apply, Hpk, Fin.mk.injEq]
  split_ifs <;> first | (exfalso; omega) | simp
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
