-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.inner_sigma_T_eq_integral_mul_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:23.027062+00:00
-- url     : https://prove2.me/submissions/3a6743b0-f4fd-482f-80e8-129b2fda29c2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_orb_cont
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_integrable_cont
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
namespace PI.UnitaryGroupMassFormula.PolyCoef
theorem _root_.solution [FiniteDimensional ℂ S] (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S)
    (f : C(UG N, ℂ)) (u : S) (w : H) (h : UG N) :
    ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ =
      ∫ x, f x * ⟪w, σ ((h * x : UG N) : Matrix (Fin N) (Fin N) ℂ) u⟫_ℂ ∂(muU N) := by
  have hint : Integrable (fun x => f x • orb hst u x) (muU N) :=
    integrable_cont (f.continuous.smul (orb_cont hrep hst u))
  unfold T
  have hL := ((innerSL ℂ w).comp ((σ (h : Matrix (Fin N) (Fin N) ℂ)).comp S.subtypeL)).integral_comp_comm hint
  refine hL.symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hmul : σ ((h * x : UG N) : Matrix (Fin N) (Fin N) ℂ) = (σ h).comp (σ x) :=
    hrep.1.2 _ (memK h) _ (memK x)
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Submodule.subtypeL_apply, orb,
    Submodule.coe_smul, map_smul, inner_smul_right, hmul, smul_eq_mul]
  try rfl
end PI.UnitaryGroupMassFormula.PolyCoef
