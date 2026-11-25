-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.trace_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:15.156734+00:00
-- url     : https://prove2.me/submissions/49ae3dd8-eb49-44bb-9c24-8ced5b63dcba

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrSumOf

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
theorem _root_.solution {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] [CommRing A] [Algebra R A] (s : S) :
    Algebra.trace A (A ⊗[R] S) (1 ⊗ₜ s) = algebraMap R A (Algebra.trace R S s) := by
  have h : Algebra.lmul A (A ⊗[R] S) (1 ⊗ₜ s) = (Algebra.lmul R S s).baseChange A := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a t
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]
end PI.ProdFormulaE.Tr
