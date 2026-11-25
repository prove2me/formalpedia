-- Prove2me | solution 1 for PI.FinKW.local_vector_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:11.791814+00:00
-- url     : https://prove2.me/submissions/fb06fc71-f57f-48ae-8867-d473e9589b4d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Theorems.Thm_PI_FinKW_coeff_psiV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinKW
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.FinKW
theorem _root_.solution : InjV := by
  classical
  intro I z hz
  apply (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E)).injective
  rw [map_zero]
  refine Finsupp.ext fun j => ?_
  rw [Finsupp.zero_apply]
  have hj : ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v
      (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E) z j) = 0 := by
    intro v
    rw [← coeff_psiV, hz v, map_zero, Finsupp.zero_apply]

  apply RestrictedProduct.ext
  intro v
  exact hj v
end PI.FinKW
