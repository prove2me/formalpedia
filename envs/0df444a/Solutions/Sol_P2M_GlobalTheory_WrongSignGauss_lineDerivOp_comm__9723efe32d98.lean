-- Prove2me | solution 1 for P2M_GlobalTheory_WrongSignGauss_lineDerivOp_comm__9723efe32d98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:04.523036+00:00
-- url     : https://prove2.me/submissions/dda71429-9b81-48dc-a510-e18b3942c342

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation
import Theorems.Thm_GlobalTheory_WrongSignGauss_sesq_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WrongSignGauss.sesq_apply

set_option autoImplicit false
open SchwartzMap LineDeriv MeasureTheory ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.WrongSignGauss
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.WrongSignGauss
theorem _root_.solution (u v : V) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (∂_{u} f) x = ∂_{u} (∂_{v} f) x := by
  have key : ∀ (u v : V) x, ∂_{v} (∂_{u} f) x = fderiv ℝ (fderiv ℝ f) x v u := by
    intro u v x
    have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
      ((SchwartzMap.fderivCLM ℝ _ ℂ f).differentiableAt (x := x)).hasFDerivAt
    have h1 := ((ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt (x := fderiv ℝ f x)).comp x hd
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have e : (⇑(∂_{u} f : 𝓢(V, ℂ))) = (ContinuousLinearMap.apply ℝ ℂ u) ∘ fderiv ℝ f := by
      funext y; rfl
    rw [e, h1.fderiv]
    rfl
  rw [key, key]
  exact ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _
end GlobalTheory.WrongSignGauss
