-- Prove2me | solution 1 for PI.WMI.lowerInv_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:42.466261+00:00
-- url     : https://prove2.me/submissions/67cc7c84-cadb-4b35-ae55-5e5fb388bca1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv
import Theorems.Thm_PI_WMI_lowerInv_torus_mem
import Theorems.Thm_PI_WMI_lowerInv_torus_mul
import Theorems.Thm_PI_WMI_lowerInv_torus_zero
import Theorems.Thm_PI_WMI_lowerInv_inner_pres
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)}
namespace PI.WMI
theorem _root_.solution (hU : IsURepOn (Kset (allPos N)) σ) (θ : Fin N → ℝ) (y w : H) :
    ⟪y, σ (torus θ) w⟫_ℂ = ⟪σ (torus (-θ)) y, w⟫_ℂ := by
  have h1 : σ (torus θ) (σ (torus (-θ)) y) = y := by
    have h := hU.1.2 (torus θ) (lowerInv_torus_mem θ) (torus (-θ)) (lowerInv_torus_mem (-θ))
    rw [lowerInv_torus_mul, add_neg_cancel, lowerInv_torus_zero, hU.1.1] at h
    have h' := congrArg (fun f : H →L[ℂ] H => f y) h
    simpa using h'.symm
  rw [← lowerInv_inner_pres hU (lowerInv_torus_mem θ) (σ (torus (-θ)) y) w, h1]
end PI.WMI
