-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.trSum_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:43.447318+00:00
-- url     : https://prove2.me/submissions/ce847880-48a7-472d-af39-f671f904b1ed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrSumOf
import Theorems.Thm_PI_ProdFormulaE_Tr_trace_one_tmul
import Theorems.Thm_PI_ProdFormulaE_Tr_trace_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
namespace PI.ProdFormulaE.Tr
theorem _root_.solution (hI : TrInj) (hS : TrSurj) : TrSum := by
  classical
  intro F _ _ ℓ _ ι _ D hD y
  let e : ℚ_[ℓ] ⊗[ℚ] F ≃ₐ[ℚ_[ℓ]] (∀ i, D.K i) :=
    AlgEquiv.ofBijective D.Φ ⟨hI F ℓ ι D hD, hS F ℓ ι D hD⟩
  have h1 : e (1 ⊗ₜ y) = fun i => D.ιF i y := by
    funext i
    simp [e, LocFam.Φ, Algebra.TensorProduct.lift_tmul]
  rw [← trace_one_tmul, ← Algebra.trace_eq_of_algEquiv e, h1, trace_pi]
end PI.ProdFormulaE.Tr
