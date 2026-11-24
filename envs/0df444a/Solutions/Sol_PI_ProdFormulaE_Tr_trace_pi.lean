-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.trace_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:40.04799+00:00
-- url     : https://prove2.me/submissions/22000a0c-8fa4-43f8-a057-bdb2e57859d7

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
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → Type*) [∀ i, CommRing (K i)] [∀ i, Algebra R (K i)] [∀ i, Module.Free R (K i)]
    [∀ i, Module.Finite R (K i)] (z : ∀ i, K i) :
    Algebra.trace R (∀ i, K i) z = ∑ i, Algebra.trace R (K i) (z i) := by
  classical
  let bs := fun i => Module.Free.chooseBasis R (K i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis bs), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (bs i), Matrix.trace]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr, bs]
end PI.ProdFormulaE.Tr
