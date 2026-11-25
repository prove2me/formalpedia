-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__iso_bd931f19b6d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:23.445921+00:00
-- url     : https://prove2.me/submissions/3fa386b0-8b99-4bf7-b6be-6ab564f7f4e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_herm0
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__iW_f2bedcc89d8d
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__iK_0f89b4e76fef
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__zero_0cf07e090cbe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_star_c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_iW_ne_iK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}
private lemma sum_phi_lemma (hk : 1 ≤ k) (X : Fin (2 * 0 + k + 1) → ℂ) :
    ∑ i, star (phiV' k 0 0 i) * (sg k i * X i) = ((Real.sqrt 2)⁻¹ : ℂ) * (X (iW k) + X (iK k)) := by
  have hWK := iW_ne_iK hk
  have h : ∀ i, star (phiV' k 0 0 i) * (sg k i * X i) =
      (if i = iW k then ((Real.sqrt 2)⁻¹ : ℂ) * X (iW k) else 0) + (if i = iK k then ((Real.sqrt 2)⁻¹ : ℂ) * X (iK k) else 0) := by
    intro i
    rcases eq_or_ne i (iW k) with rfl | h1
    · rw [phi'_iW hk, star_c, if_pos rfl, if_neg hWK, add_zero]
      simp [sg, hWK]
    · rcases eq_or_ne i (iK k) with rfl | h2
      · rw [phi'_iK hk, star_neg, star_c, if_neg h1, if_pos rfl, zero_add]
        simp [sg]
      · rw [phi'_zero hk i h1 h2, star_zero, zero_mul, if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (hk : 1 ≤ k) : herm (Hpk k 0) (phiV' k 0 0) (phiV' k 0 0) = 0 := by
  rw [herm0, sum_phi_lemma hk, phi'_iW hk, phi'_iK hk]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
