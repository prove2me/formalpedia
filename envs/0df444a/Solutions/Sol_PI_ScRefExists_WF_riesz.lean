-- Prove2me | solution 1 for PI.ScRefExists.WF.riesz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:18:48.053568+00:00
-- url     : https://prove2.me/submissions/39c30d1f-15de-472c-985d-5cf304138c8a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Theorems.Thm_PI_ScRefExists_WF_hG_def
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
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open Matrix
open PI PI.ScRefExists PI.ScRefExists.WF
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.WF
theorem _root_.solution (c : (Fin I.n → I.E) →ₗ[I.E] I.E) : ∃ u : Fin I.n → I.E, ∀ x, hG I u x = c x := by
  let w : Fin I.n → I.E := fun j => c (Pi.single j 1)
  refine ⟨fun i => star ((w ᵥ* I.J⁻¹) i), fun x => ?_⟩
  have hJ : I.J⁻¹ * I.J = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr I.J_det)
  have hx : x = ∑ j, x j • Pi.single j (1 : I.E) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hc : c x = ∑ j, x j * w j := by
    conv_lhs => rw [hx]
    simp [map_sum, map_smul, w]
  have hw : (w ᵥ* I.J⁻¹) ᵥ* I.J = w := by
    rw [Matrix.vecMul_vecMul, hJ, Matrix.vecMul_one]
  rw [hc, hG_def]
  simp only [star_star]
  calc ∑ i, ∑ j, (w ᵥ* I.J⁻¹) i * I.J i j * x j = ∑ j, ((w ᵥ* I.J⁻¹) ᵥ* I.J) j * x j := by
        rw [Finset.sum_comm]
        simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]
    _ = ∑ j, x j * w j := by
        rw [hw]
        simp only [mul_comm]
end PI.ScRefExists.WF
