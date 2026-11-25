-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__dot_d29ba0cfc144
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:25:55.812255+00:00
-- url     : https://prove2.me/submissions/16f6da2e-492a-4774-916c-4dc5a42b0748

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__iW_f2bedcc89d8d
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__iK_0f89b4e76fef
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__zero_0cf07e090cbe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_normSq_c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_dot_star_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_iW_ne_iK


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
variable {k : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (hk : 1 ≤ k) : star (phiV' k 0 0) ⬝ᵥ phiV' k 0 0 = 1 := by
  have hWK := iW_ne_iK hk
  have hφ : ∀ i, Complex.normSq (phiV' k 0 0 i) =
      (if i = iW k then 1 / 2 else 0) + (if i = iK k then 1 / 2 else 0) := by
    intro i
    rcases eq_or_ne i (iW k) with rfl | h1
    · rw [phi'_iW hk, normSq_c, if_pos rfl, if_neg hWK, add_zero]
    · rcases eq_or_ne i (iK k) with rfl | h2
      · rw [phi'_iK hk, Complex.normSq_neg, normSq_c, if_neg h1, if_pos rfl, zero_add]
      · rw [phi'_zero hk i h1 h2, map_zero, if_neg h1, if_neg h2, add_zero]
  rw [dot_star_self, Finset.sum_congr rfl fun i _ => hφ i, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
