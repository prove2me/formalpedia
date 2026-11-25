-- Prove2me | solution 1 for PI.BesselDerivW.exp_entry_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:03.078096+00:00
-- url     : https://prove2.me/submissions/666b3d27-cb04-42e0-91a2-d695e2c035f2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ContDiffOnDirectionalDerivative
import Definitions.Def_Formalism_PeriodIntegrals_BesselDeriv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ExpSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Matrix
noncomputable section
open PI PI.BesselDerivW
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open scoped Matrix.Norms.Operator
namespace PI.BesselDerivW
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X))
      (NormedSpace.exp ((t : ℂ) • X) * X) t := by
    intro t
    have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = fun u : ℝ => NormedSpace.exp (u • X) := by
      funext t; rw [Complex.coe_smul]
    rw [e, Complex.coe_smul]
    exact hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  set f := fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) with hf
  have hdiff : Differentiable ℝ f := fun t => (hd t).differentiableAt
  have hder : deriv f = fun t => f t * X := funext fun t => (hd t).deriv
  have hcd : ∀ m : ℕ, ContDiff ℝ m f := by
    intro m
    induction m with
    | zero => exact (contDiff_zero.2 hdiff.continuous).of_le (by simp)
    | succ m ih =>
      have h' : ContDiff ℝ m (deriv f) := by rw [hder]; exact ih.mul contDiff_const
      have h1 : ContDiff ℝ ((m : WithTop ℕ∞) + 1) f := by
        first
        | exact contDiff_succ_iff_deriv.2 ⟨hdiff, by simp, h'⟩
        | exact contDiff_succ_iff_deriv.2 ⟨hdiff, h'⟩
      exact h1.of_le (by norm_num)
  have hcf : ContDiff ℝ ∞ f := contDiff_infty.2 hcd
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff.comp hcf
end PI.BesselDerivW
