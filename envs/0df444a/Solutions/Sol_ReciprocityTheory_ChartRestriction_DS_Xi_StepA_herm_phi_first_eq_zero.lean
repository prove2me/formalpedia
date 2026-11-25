-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.herm_phi_first_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:49.126989+00:00
-- url     : https://prove2.me/submissions/128ff505-3f09-47c8-994c-86ac71a860c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
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
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section lev
variable (k r' : ℕ)
private lemma herm_bvec_right' {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (b : Fin m) :
    herm H v (bvec b) = ∑ j, H b j * v j := by
  have hs : star (bvec b) = bvec b := by
    funext i
    by_cases h : i = b
    · subst h; simp [bvec]
    · simp [bvec, h]
  unfold herm
  rw [hs]
  simp [bvec, dotProduct, Matrix.mulVec, Pi.single_apply]
private lemma sum_Hpk_eI_a0_mul_eq_esI (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ j, Hpk k (1 + r') (eI k (1 + r') (a0 r')) j * w j = w (esI k (1 + r') (a0 r')) := by
  rw [Finset.sum_eq_single (esI k (1 + r') (a0 r'))]
  · have h1 : Hpk k (1 + r') (eI k (1 + r') (a0 r')) (esI k (1 + r') (a0 r')) = 1 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 2 * (1 + r') + k := fun h => hj (Fin.ext (by simp only [esI, a0, Fin.val_mk]; omega))
    have h0 : Hpk k (1 + r') (eI k (1 + r') (a0 r')) j = 0 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
private lemma sum_Hpk_esI_a0_mul_eq_eI (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ j, Hpk k (1 + r') (esI k (1 + r') (a0 r')) j * w j = w (eI k (1 + r') (a0 r')) := by
  rw [Finset.sum_eq_single (eI k (1 + r') (a0 r'))]
  · have h1 : Hpk k (1 + r') (esI k (1 + r') (a0 r')) (eI k (1 + r') (a0 r')) = 1 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 0 := fun h => hj (Fin.ext (by simp only [eI, a0, Fin.val_mk]; omega))
    have h0 : Hpk k (1 + r') (esI k (1 + r') (a0 r')) j = 0 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end lev
section dl
variable (k r : ℕ)
end dl
section a1
variable (k r' : ℕ)
end a1
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (b : Fin (1 + r' + 1)) : herm (Hpk k (1 + r')) (phiV' k (1 + r') b) (e0 k r') = 0 := by
  simp only [e0]
  rw [herm_bvec_right', sum_Hpk_eI_a0_mul_eq_esI]
  simp only [phiV', Matrix.mulVec, dotProduct]
  rw [sum_Hpk_esI_a0_mul_eq_eI]
  simp only [phiV]
  split_ifs with hb
  · simp only [bvec, Pi.single_apply, esI, eI, a0, Fin.val_mk, Fin.ext_iff]
    (try split_ifs) <;> (first | rfl | omega)
  · simp only [epsV, Pi.smul_apply, Pi.add_apply, bvec, Pi.single_apply, wI, eI, a0, Fin.val_mk,
      Fin.ext_iff, Fin.val_zero, Fin.val_last]
    (try split_ifs) <;> (first | omega | simp)
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
