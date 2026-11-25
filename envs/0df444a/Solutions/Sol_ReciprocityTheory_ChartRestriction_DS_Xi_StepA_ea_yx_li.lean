-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_yx_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:49:42.783666+00:00
-- url     : https://prove2.me/submissions/3284b0d2-f258-43e0-bd39-c4d3ea867705

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_gv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_rankOne_mem_unitary
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__li_6fbc45786d0f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_yx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_hinv_gv
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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
private theorem hpk_sq_lemma (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hm : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · simp only [and_true, true_and, Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | (simp; done) | norm_num
    · intro l _ hl
      have hl' : l.val ≠ i.val := fun h => hl (Fin.ext h)
      have : Hpk k r i l = 0 := by
        simp only [and_true, true_and, Hpk, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · simp only [and_true, true_and, Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | (simp; done) | norm_num
    · intro l _ hl
      have hl' : l.val ≠ 2 * r + k - i.val := fun h => hl (Fin.ext h)
      have : Hpk k r i l = 0 := by
        simp only [and_true, true_and, Hpk, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
private theorem eq_zero_of_mulVec_eq_zero_of_mem_GV {k r : ℕ} {M : Mat k r} (hM : M ∈ GV k r) (u : Fin (2 * r + k + 1) → ℂ)
    (hu : M *ᵥ u = 0) : u = 0 := by
  have h : Mᴴ * Hpk k r * M = Hpk k r := hM
  have e : Hpk k r *ᵥ u = 0 := by
    rw [← h, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
  have e2 : u = (Hpk k r * Hpk k r) *ᵥ u := by rw [hpk_sq_lemma, Matrix.one_mulVec]
  rw [e2, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r' : ℕ} (hk : 1 ≤ k) (hHI : HeisInv) (hHM : HeisMem) (hOSM : OneStepMem) (x : HPar k r') :
    LinearIndependent ℂ (Yx k r' x) := by
  have hM : ((heis0 k r' x)⁻¹ * w0 k r' 1) ∈ GV k (1 + r') :=
    ea_gv_mul (ea_hinv_gv hHI hHM x) (rankOne_mem_unitary hOSM (one_ne_zero : (1 : ℂ) ≠ 0))
  have hli := ea_phiV'_li (k := k) (r := 1 + r') hk
  have e : Yx k r' x = fun a => ((heis0 k r' x)⁻¹ * w0 k r' 1) *ᵥ phiV' k (1 + r') a :=
    funext (ea_yx k r' x)
  rw [e]
  exact hli.map' (Matrix.mulVecLin _) (LinearMap.ker_eq_bot'.2 (eq_zero_of_mulVec_eq_zero_of_mem_GV hM))
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
