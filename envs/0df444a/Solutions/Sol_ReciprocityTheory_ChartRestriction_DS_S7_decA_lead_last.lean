-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.decA_lead_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:03.987658+00:00
-- url     : https://prove2.me/submissions/f0a09195-94c2-482e-a2ba-08f78a4dbdc1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_decA_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_decA_lead_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ} (hYp : inP ε Y)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) :
    (lead n (NormedSpace.exp Y)).re = 1 := by
  obtain ⟨_, h2⟩ := hYp
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have htr : Matrix.trace Y = 0 := by
    have e1 : Matrix.trace Y = Matrix.trace (Jm ε * (Y * Jm ε)) := by
      rw [← Matrix.trace_mul_comm (Y * Jm ε) (Jm ε), Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [h2, Matrix.mul_neg, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, Matrix.trace_neg] at e1
    have e2 : (2 : ℂ) * Matrix.trace Y = 0 := by linear_combination e1
    simpa using e2
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have hsum : ∑ j, y j = 0 := by
    have e3 : Matrix.trace Y = ((∑ j, y j : ℝ) : ℂ) := by
      rw [hY, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal]
      push_cast
      rfl
    rw [htr] at e3
    exact_mod_cast e3.symm
  rw [hY, decA_exp hU y, decA_lead_re y n le_rfl]
  have huniq : ∀ J : {J : Finset (Fin n) // J.card = n}, J = ⟨Finset.univ, by simp⟩ :=
    fun J => Subtype.ext (Finset.eq_univ_of_card _ (by simpa using J.2))
  rw [Fintype.sum_eq_single ⟨Finset.univ, by simp⟩ (fun J hJ => absurd (huniq J) hJ)]
  rw [hsum, Real.exp_zero, mul_one]
  unfold dmW
  have hid : ((Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp) : Fin n → Fin n) = id :=
    (Finset.orderEmbOfFin_unique (by simp) (fun x => Finset.mem_univ x) strictMono_id).symm
  have hsub : U.submatrix (Fin.castLE (le_refl n))
      ((Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp)) = U := by
    ext i j
    rw [Matrix.submatrix_apply, show Fin.castLE (le_refl n) i = i from Fin.ext rfl,
      show ((Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp) : Fin n → Fin n) j = j from congrFun hid j]
  rw [hsub]
  have hdet : star U.det * U.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hUU, Matrix.det_one]
  have h5 : ((‖U.det‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hdet, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  exact_mod_cast h5
end ReciprocityTheory.ChartRestriction.DS.S7
