-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.ccb_diffAt_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:26:24.080795+00:00
-- url     : https://prove2.me/submissions/962be1c5-ad2c-4628-ba86-97fd7b929dc4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (m : Matrix (Fin n) (Fin n) ℂ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : IsUnit g) : DifferentiableAt ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹ * m) g := by
  have hdet : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp hg).ne_zero
  have hentry : ∀ a b : Fin n,
      Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
    intro a b
    exact (differentiable_apply (𝕜 := ℂ) (F' := fun _ : Fin n => ℂ) b).comp
      (differentiable_apply (𝕜 := ℂ) (F' := fun _ : Fin n => Fin n → ℂ) a)
  have hD : ∀ M : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
      (∀ a b, Differentiable ℂ (fun z => M z a b)) → Differentiable ℂ (fun z => (M z).det) := by
    intro M hM
    simp_rw [det_apply']
    refine Differentiable.fun_sum fun σ _ => ?_
    refine (differentiable_const _).mul ?_
    intro z
    exact (HasFDerivAt.finsetProd (u := univ) (g := fun j w => M w (σ j) j)
      fun j _ => (hM _ _ z).hasFDerivAt).differentiableAt
  have hA : ∀ i k, Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => z.adjugate i k) := by
    intro i k
    simp only [adjugate_apply]
    refine hD _ fun a b => ?_
    simp only [updateRow_apply]
    by_cases hab : a = k
    · simp only [hab, if_true]; exact differentiable_const _
    · simp only [hab, if_false]; exact hentry a b
  have e : (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹ * m) =
      fun z => Matrix.of fun i j => ∑ k, ((z.det)⁻¹ * z.adjugate i k) * m k j := by
    funext z
    ext i j
    simp [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.mul_apply, Matrix.smul_apply]
  rw [e]
  have h : DifferentiableAt ℂ (fun z : Matrix (Fin n) (Fin n) ℂ =>
      (fun i j => ∑ k, ((z.det)⁻¹ * z.adjugate i k) * m k j : Fin n → Fin n → ℂ)) g := by
    refine differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j => ?_
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((((hD (fun z => z) hentry).differentiableAt.inv hdet).mul
      (hA i k).differentiableAt).mul_const _)
  exact h
end ReciprocityTheory.ChartRestriction.DS.S7
