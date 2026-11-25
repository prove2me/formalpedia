-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.rep0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:44.285801+00:00
-- url     : https://prove2.me/submissions/4c0e033e-cf50-4766-adc7-d1d16a13ed6d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange

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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}
variable (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b)) :
    m *ᵥ phiV k r' 0 = τ 0 0 • (κ *ᵥ phiV k r' 0) := by
  rw [hrep 0, Finset.sum_eq_single 0]
  · intro b _ hb
    rw [hτ (show id (0 : Fin (r' + 1)) < id b from lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hb)),
      zero_smul]
  · intro h
    exact absurd (Finset.mem_univ 0) h
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
