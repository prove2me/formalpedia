-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.LocFam.injective_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:35.986486+00:00
-- url     : https://prove2.me/submissions/cbf6ca6a-1c08-4f96-8d2f-ad9d05459437

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_InjectiveOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}
namespace PI.ProdFormulaE.Tr
namespace LocFam
theorem _root_.solution [Fintype ι] (D : LocFam F ℓ ι)
    (hl : LinearIndependent ℚ_[ℓ] (fun k => D.Φ (1 ⊗ₜ integralBasis F k))) :
    Function.Injective D.Φ := by
  classical
  set bb := Algebra.TensorProduct.basis ℚ_[ℓ] (integralBasis F) with hbb
  have hb : ∀ k, bb k = 1 ⊗ₜ integralBasis F k := fun k => Algebra.TensorProduct.basis_apply _ _
  refine (injective_iff_map_eq_zero D.Φ).2 fun x hx => ?_
  rw [← bb.sum_repr x] at hx ⊢
  simp only [map_sum, map_smul, hb] at hx
  have h0 := (Fintype.linearIndependent_iff.1 hl) (fun k => bb.repr x k) hx
  simp [h0]
end LocFam
end PI.ProdFormulaE.Tr
