-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.herm_sum_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:23:27.024192+00:00
-- url     : https://prove2.me/submissions/83dcff16-5d29-46eb-a066-4c297c2589f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
theorem _root_.solution {α : Type*} (c : α → ℂ) (s : Finset α) (u : ι → ℂ) (w : α → ι → ℂ) :
    herm H u (∑ j ∈ s, c j • w j) = ∑ j ∈ s, star (c j) * herm H u (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [herm, star_add, star_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
