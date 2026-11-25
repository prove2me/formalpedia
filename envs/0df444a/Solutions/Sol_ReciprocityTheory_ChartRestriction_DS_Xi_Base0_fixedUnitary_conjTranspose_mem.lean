-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.fixedUnitary_conjTranspose_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:13:43.375372+00:00
-- url     : https://prove2.me/submissions/c2158965-54a6-423b-961b-4240b00df89d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_fixedUnitary_projection_identities
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_mem_fixedUnitary_of_unitary_fixes

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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) : hᴴ ∈ U0 k := by
  obtain ⟨hu, -, hsP, -⟩ := fixedUnitary_projection_identities hh
  refine mem_fixedUnitary_of_unitary_fixes ?_ hsP
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp hu
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
