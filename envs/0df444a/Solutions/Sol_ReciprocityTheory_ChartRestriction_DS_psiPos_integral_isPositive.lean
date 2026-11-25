-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.psiPos_integral_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:42.935277+00:00
-- url     : https://prove2.me/submissions/b7b1bd98-4c4a-42b3-9a92-54395bc918c4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_KinstSecondCountable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_PsiPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_psiPos_inner_P

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open S7
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (T : KType ε Λ) {c : ℝ} (hc : 0 ≤ c) (g : KG ε → ℝ)
    (hg0 : ∀ k, 0 ≤ g k) :
    ((c : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)).IsPositive := by
  set A : T.V →L[ℂ] T.V :=
    (c : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε) with hA

  have key : ∀ x : T.V, ∃ r : ℝ, 0 ≤ r ∧ ⟪x, A x⟫_ℂ = (r : ℂ) := by
    intro x
    by_cases hint : Integrable (fun k => ((g k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹)) (muK ε)
    · refine ⟨c * ∫ k, g k * ‖⟪T.op k T.w, x⟫_ℂ‖ ^ 2 ∂(muK ε), ?_, ?_⟩
      · exact mul_nonneg hc (integral_nonneg fun k => mul_nonneg (hg0 k) (sq_nonneg _))
      · have hpt : ∀ k, ⟪x, (((g k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹)) x⟫_ℂ =
            ((g k * ‖⟪T.op k T.w, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
          intro k
          rw [ContinuousLinearMap.smul_apply, inner_smul_right, psiPos_inner_P, Complex.ofReal_mul]
        rw [hA, ContinuousLinearMap.smul_apply, inner_smul_right,
          ContinuousLinearMap.integral_apply hint x,
          ← integral_inner (hint.apply_continuousLinearMap x)]
        simp_rw [hpt]
        rw [Complex.ofReal_mul]
        first
          | rw [integral_complex_ofReal]
          | exact congrArg _ integral_ofReal
    · refine ⟨0, le_rfl, ?_⟩
      rw [hA, integral_undef hint, smul_zero, ContinuousLinearMap.zero_apply, inner_zero_right,
        Complex.ofReal_zero]
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  obtain ⟨r, hr, hx⟩ := key x
  have hx' : ⟪A x, x⟫_ℂ = (r : ℂ) := by
    rw [← inner_conj_symm, hx, Complex.conj_ofReal]
  rw [hx']
  refine ⟨?_, ?_⟩
  · simp
  · simpa using hr
end ReciprocityTheory.ChartRestriction.DS
