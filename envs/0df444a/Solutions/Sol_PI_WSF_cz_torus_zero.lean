-- Prove2me | solution 1 for PI.WSF.cz_torus_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:18.005902+00:00
-- url     : https://prove2.me/submissions/92b00252-cd1f-4a3f-ac3d-87d8337889c2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CzDiagUnitary
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


section
noncomputable section
namespace PI.WSF
open MvPolynomial Matrix
open scoped ComplexOrder
private theorem setOf_norm_eq_one_infinite : ({z : ℂ | ‖z‖ = 1} : Set ℂ).Infinite := by
  have hI : (Set.Ioc (-Real.pi) Real.pi).Infinite := Set.Ioc_infinite (by linarith [Real.pi_pos])
  refine Set.infinite_of_injOn_mapsTo
    (f := fun θ : ℝ => Complex.cos θ + Complex.sin θ * Complex.I) ?_ ?_ hI
  · intro a ha b hb hab
    have h1 := congrArg Complex.arg hab
    simp only at h1
    rwa [Complex.arg_cos_add_sin_mul_I ha, Complex.arg_cos_add_sin_mul_I hb] at h1
  · intro θ _
    exact Complex.norm_cos_add_sin_mul_I θ
end PI.WSF
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WSF
open MvPolynomial Matrix
open scoped ComplexOrder
namespace PI.WSF
theorem _root_.solution {ι : Type*} [Fintype ι] (Q : MvPolynomial ι ℂ)
    (h : ∀ z : ι → ℂ, (∀ i, ‖z i‖ = 1) → eval z Q = 0) : Q = 0 := by
  rw [MvPolynomial.funext_set_iff (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => setOf_norm_eq_one_infinite)]
  intro x hx
  rw [map_zero]
  exact h x (fun i => hx i (Set.mem_univ i))
end PI.WSF
