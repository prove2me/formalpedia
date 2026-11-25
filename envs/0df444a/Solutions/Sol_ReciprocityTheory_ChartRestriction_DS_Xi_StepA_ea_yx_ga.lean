-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_yx_ga
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:40:05.438104+00:00
-- url     : https://prove2.me/submissions/a652715c-b294-460e-8d92-2793abcdd33c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_StarLastDotLast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_ga_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_ga_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_UH_mul_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_last_basis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_levi_fixes_last_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r' : ℕ} (hHM : HeisMem) (x : HPar k r') :
    0 < Ga k (1 + r') 0 (Yx k r' x) ∧ ∀ l, 0 ≤ Ga k (1 + r') l (Yx k r' x) := by
  refine ⟨?_, fun l => ea_ga_nonneg _ l⟩
  rw [ea_ga_zero]
  have hY0 : Yx k r' x 0 = (heis0 k r' x)⁻¹ *ᵥ es0 k r' := by rw [Yx, phi2, phiV_zero, levi_fixes_last_basis]
  have hne : Yx k r' x 0 ≠ 0 := by
    intro h
    have h1 : heis0 k r' x *ᵥ Yx k r' x 0 = es0 k r' := by
      rw [hY0, mulVec_mulVec, UH_mul_inv k (1 + r') (hHM k r' x).1, one_mulVec]
    rw [h, mulVec_zero] at h1
    have h2 := congrFun h1 ⟨2 * (1 + r') + k, by omega⟩
    simp [last_basis_apply] at h2
  exact (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hne)).1
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
