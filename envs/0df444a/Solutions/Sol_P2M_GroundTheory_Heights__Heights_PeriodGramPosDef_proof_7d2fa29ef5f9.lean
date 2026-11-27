-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_proof_7d2fa29ef5f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:06.740643+00:00
-- url     : https://prove2.me/submissions/f6fd5a71-0207-407b-8aeb-aa67abde8b8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodGramPosDef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_symm_5f1a589f163b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_qf_gram_22a36bb6f9bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_sum_periodBasis_22203320f3fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_qf_nonneg_d6a602480fda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_transpose_eq_of_posSemidef_d388a88d8b69


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open PeriodGramPosDef
namespace GroundTheory.Heights₂.Heights
namespace PeriodGramPosDef
theorem _root_.solution (hPH : PeriodHermValue.Statement) : PeriodGramPosDef.Statement := by
  intro g τ hY
  have hu : IsUnit (τ.map Complex.im).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit
  have hform : ∀ x : Fin (g + g) → ℝ,
      MCSchur.qf (periodGram τ) x =
        MCSchur.qf (τ.map Complex.im)⁻¹
            ((fun k => x (Fin.castAdd g k)) + τ.map Complex.re *ᵥ fun k => x (Fin.natAdd g k)) +
          MCSchur.qf (τ.map Complex.im) (fun k => x (Fin.natAdd g k)) := by
    intro x
    rw [periodGram, qf_gram, sum_periodBasis]
    exact hPH g τ hu _ _
  refine ⟨?_, hform⟩
  have hYi := hY.inv
  have hsym : ((τ.map Complex.im)⁻¹)ᵀ = (τ.map Complex.im)⁻¹ :=
    MCCusp.transpose_eq_of_posSemidef hYi.posSemidef
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [transpose_apply, periodGram, Matrix.of_apply]
    exact hermPair_symm hsym _ _
  · have e : star x ⬝ᵥ (periodGram τ *ᵥ x) = MCSchur.qf (periodGram τ) x := by
      simp [MCSchur.qf]
    rw [e, hform]
    have h1 := MCCusp.qf_nonneg hYi.posSemidef
      ((fun k => x (Fin.castAdd g k)) + τ.map Complex.re *ᵥ fun k => x (Fin.natAdd g k))
    by_cases hβ : (fun k => x (Fin.natAdd g k)) = 0
    · have hα : (fun k => x (Fin.castAdd g k)) ≠ 0 := by
        intro hα
        apply hx
        funext i
        refine Fin.addCases (fun k => ?_) (fun k => ?_) i
        · exact congrFun hα k
        · exact congrFun hβ k
      have h2 : 0 < MCSchur.qf (τ.map Complex.im)⁻¹ (fun k => x (Fin.castAdd g k)) := by
        have := hYi.dotProduct_mulVec_pos hα
        simpa [MCSchur.qf] using this
      rw [hβ, mulVec_zero, add_zero]
      rw [hβ, mulVec_zero, add_zero] at h1
      have h3 : MCSchur.qf (τ.map Complex.im) 0 = 0 := by simp [MCSchur.qf]
      rw [h3]
      linarith
    · have h2 : 0 < MCSchur.qf (τ.map Complex.im) (fun k => x (Fin.natAdd g k)) := by
        have := hY.dotProduct_mulVec_pos hβ
        simpa [MCSchur.qf] using this
      linarith
end PeriodGramPosDef
end GroundTheory.Heights₂.Heights
