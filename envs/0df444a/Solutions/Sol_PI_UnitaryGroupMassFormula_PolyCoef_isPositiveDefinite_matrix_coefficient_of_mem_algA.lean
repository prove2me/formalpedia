-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.isPositiveDefinite_matrix_coefficient_of_mem_algA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:02.207819+00:00
-- url     : https://prove2.me/submissions/549d8a13-e478-4a94-8b80-9b9680d23bb6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_orb_cont
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_integrable_cont
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_inner_sigma_T_eq_integral_mul_inner
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_const
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_const
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_sep_of_mem
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
namespace PI.UnitaryGroupMassFormula.PolyCoef
theorem _root_.solution [FiniteDimensional ℂ S] (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S)
    {f : C(UG N, ℂ)} (hf : f ∈ algA N) (u : S) (w : H) :
    IsPD (fun h : UG N => ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ) := by
  obtain ⟨ι, _, a, b, ha, hb, hab⟩ := sep_of_mem hf
  have hcont : Continuous (fun y : UG N => ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ) :=
    continuous_const.inner (continuous_subtype_val.comp (orb_cont hrep hst u))
  have hfun : ∀ h : UG N, ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ = ∑ i, a i h *
      ∫ y, b i y * ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ ∂(muU N) := by
    intro h
    rw [inner_sigma_T_eq_integral_mul_inner hrep hst f u w h]
    have hsh := integral_mul_left_eq_self (μ := muU N)
      (fun y => f (h⁻¹ * y) * ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ) h
    simp only [inv_mul_cancel_left] at hsh
    rw [hsh]
    simp_rw [hab h, Finset.sum_mul]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    · intro i _
      exact integrable_cont ((continuous_const.mul (hb i)).mul hcont)
  have e : (fun h : UG N => ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ) = fun h => ∑ i, a i h *
      ∫ y, b i y * ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ ∂(muU N) := funext hfun
  rw [e]
  exact IsPD.sum _ fun i _ => (ha i).mul (IsPD.const _)
end PI.UnitaryGroupMassFormula.PolyCoef
