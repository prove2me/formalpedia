-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin.hpk_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:36.379986+00:00
-- url     : https://prove2.me/submissions/6e0cd70f-ad58-4cef-a941-ecc163292085

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
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


section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ThFin
private lemma conjTranspose_Hpk_eq_Hpk (k r' : ℕ) : (Hpk k r')ᴴ = Hpk k r' := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | rfl | norm_num
private lemma Hpk_sq_eq_one (k r' : ℕ) : Hpk k r' * Hpk k r' = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hσ : (if (i : ℕ) < r' ∨ r' + k < (i : ℕ) then 2 * r' + k - i else (i : ℕ)) < 2 * r' + k + 1 := by
    split_ifs <;> omega
  rw [Finset.sum_eq_single ⟨_, hσ⟩]
  · simp only [Hpk, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | rfl | norm_num
  · intro l _ hl
    have h0 : Hpk k r' i l = 0 := by
      simp only [Hpk, Matrix.of_apply, ne_eq, Fin.ext_iff] at hl ⊢
      split_ifs at hl ⊢ <;> first | (exfalso; omega) | rfl
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end ThFin
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
theorem _root_.solution (k r' : ℕ) : Hpk k r' ∈ GV k r' := by
  simp only [GV, UH, Set.mem_setOf_eq]
  rw [conjTranspose_Hpk_eq_Hpk, Hpk_sq_eq_one, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
