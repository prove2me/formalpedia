-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.sum_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:31.237812+00:00
-- url     : https://prove2.me/submissions/53b2ccea-4241-4931-acb4-e10fcb7377b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec

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
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution {n N : ℕ} (h : N = n + 2) (f : Fin N → ℂ) (h0 : ∀ q : Fin N, q.val = 0 → f q = 0)
    (h1 : ∀ q : Fin N, q.val = n + 1 → f q = 0) : ∑ q, f q = ∑ q : Fin n, f ⟨q.val + 1, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, h0 0 rfl, h1 (Fin.last n).succ (by simp)]
  simp only [zero_add, add_zero]; rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
