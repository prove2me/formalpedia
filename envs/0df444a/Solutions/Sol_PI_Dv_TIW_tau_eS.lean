-- Prove2me | solution 1 for PI.Dv.TIW.tau_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:59:07.313348+00:00
-- url     : https://prove2.me/submissions/acc90489-4a81-4911-b840-864f9382e6e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Theorems.Thm_PI_Dv_TIW_mul_eS
import Theorems.Thm_PI_Dv_TIW_eS_central
import Theorems.Thm_PI_Dv_TIW_tau_central_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
namespace PI.Dv.TIW
theorem _root_.solution [CharZero K] : (T.tau s).asAlgebraHom (eS T s) = 1 := by
  obtain ⟨μ, hμ⟩ := tau_central_scalar T s (eS T s) (eS_central T s)
  set d := Module.finrank K (T.W s) with hd
  have hd0 : (d : K) ≠ 0 := by
    have : 0 < d := Module.finrank_pos
    exact_mod_cast this.ne'
  have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero

  set Ξ : Module.End K (Module.End K (T.W s)) := ∑ y : G,
    (((d : K) / ((Fintype.card G : ℕ) : K)) •
      ((LinearMap.trace K (T.W s)) ∘ₗ LinearMap.mulLeft K (T.tau s y⁻¹))).smulRight (T.tau s y) with hΞ
  have hΞapp : ∀ M, Ξ M = (T.tau s).asAlgebraHom (theta T s M) := by
    intro M
    rw [hΞ, theta, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, Representation.asAlgebraHom_of, LinearMap.smulRight_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_eq_mul]
  have hΞμ : Ξ = μ • LinearMap.id := by
    apply LinearMap.ext; intro M
    obtain ⟨z, rfl⟩ := T.irr s M
    rw [hΞapp, ← mul_eS, map_mul, hμ]
    simp
  have htr := congrArg (LinearMap.trace K _) hΞμ
  rw [hΞ, map_sum, map_smul, LinearMap.trace_id, Module.finrank_linearMap] at htr
  simp only [LinearMap.trace_smulRight, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    ← map_mul, inv_mul_cancel, map_one, LinearMap.trace_one, smul_eq_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at htr
  have : μ = 1 := by
    rw [← hd] at htr
    push_cast at htr
    field_simp at htr
    first
    | exact htr.symm
    | exact htr
    | (have h2 : (d : K) * d ≠ 0 := mul_ne_zero hd0 hd0
       apply mul_right_cancel₀ h2
       linear_combination -htr)
  rw [hμ, this, one_smul]
end PI.Dv.TIW
