-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dtau_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:56.997622+00:00
-- url     : https://prove2.me/submissions/10bb10a5-1941-43f9-b9ba-69699c61c0b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_op_inv_eq_adjoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inK_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_gamma_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_exists_oneParam


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
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    ContinuousLinearMap.adjoint (T.dτ A) = -T.dτ A := by
  obtain ⟨γ, -, hγ, hmul⟩ := exists_oneParam ε hA
  have h0 := gamma_zero hmul
  have hinv : ∀ t, γ (-t) = (γ t)⁻¹ := fun t =>
    eq_inv_of_mul_eq_one_left (by rw [← hmul, neg_add_cancel, h0])
  have h1 := T.hasDeriv A hA γ hγ
  have h2 := T.hasDeriv (-A) (inK_neg hA) (fun t => γ (-t)) (fun t => by
    rw [hγ]; congr 1; push_cast; rw [neg_smul, smul_neg])
  have h3 := h1.star
  simp only [ContinuousLinearMap.star_eq_adjoint] at h3
  have e : (fun t => ContinuousLinearMap.adjoint (T.op (γ t))) = fun t => T.op (γ (-t)) :=
    funext fun t => by rw [← op_inv_eq_adjoint, hinv]
  rw [e] at h3
  rw [h3.unique h2, map_neg]
end ReciprocityTheory.ChartRestriction.DS.S7
