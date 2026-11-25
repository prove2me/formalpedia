-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.yx_ga
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:57.108793+00:00
-- url     : https://prove2.me/submissions/8f6dcd72-2b40-4f41-84ae-e521687f2c15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_StarLastDotLast
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergRankOneDecomposition
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_yx_ga


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
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (hB2 : InductiveHeisenbergInputs) (hIW : IW) (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') :
    0 < Ga k (1 + r') 0 (Yx k r' x) ∧ ∀ l, 0 ≤ Ga k (1 + r') l (Yx k r' x) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hHM, -⟩ := hB2
  exact ea_yx_ga hHM x
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
