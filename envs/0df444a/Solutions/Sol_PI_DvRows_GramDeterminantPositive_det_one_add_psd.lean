-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.det_one_add_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:17.316177+00:00
-- url     : https://prove2.me/submissions/06cb82c4-3e4a-4e28-9091-ca88140cab00

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution {N : Matrix n n ℂ} (hN : N.PosSemidef) :
    ∃ t : ℝ, 1 ≤ t ∧ (1 + N).det = (t : ℂ) := by
  have hH := hN.isHermitian
  have hs := hH.spectral_theorem
  set U := hH.eigenvectorUnitary with hUdef
  have hU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem U.2
  have key : 1 + N = (U : Matrix n n ℂ) * (1 + diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *
      star (U : Matrix n n ℂ) := by
    conv_lhs => rw [hs]
    rw [Unitary.conjStarAlgAut_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU]
  have hdU : (U : Matrix n n ℂ).det * (star (U : Matrix n n ℂ)).det = 1 := by
    rw [← det_mul, hU, det_one]
  refine ⟨∏ i, (1 + hH.eigenvalues i), ?_, ?_⟩
  · calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i _ => by linarith [hN.eigenvalues_nonneg i])
  · rw [key, det_mul, det_mul]
    have h1 : (1 + diagonal (RCLike.ofReal ∘ hH.eigenvalues) : Matrix n n ℂ) =
        diagonal (fun i => ((1 + hH.eigenvalues i : ℝ) : ℂ)) := by
      rw [← diagonal_one, diagonal_add]; congr 1; funext i; simp
    rw [h1, det_diagonal]
    calc (U : Matrix n n ℂ).det * (∏ i, ((1 + hH.eigenvalues i : ℝ) : ℂ)) *
          (star (U : Matrix n n ℂ)).det
        = (∏ i, ((1 + hH.eigenvalues i : ℝ) : ℂ)) * ((U : Matrix n n ℂ).det *
          (star (U : Matrix n n ℂ)).det) := by ring
      _ = _ := by rw [hdU, mul_one]; push_cast; rfl
end PI.DvRows.GramDeterminantPositive
