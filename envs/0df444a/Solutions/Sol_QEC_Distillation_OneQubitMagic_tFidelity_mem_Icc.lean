-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tFidelity_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:13:45.728987+00:00
-- url     : https://prove2.me/submissions/efb298c2-9b12-48dc-bd39-65582224b461

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tDirectionFidelity_mem_Icc

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (rho : DensityOperator QubitSpace) :
    tFidelity rho ∈ Set.Icc 0 1 := by
  unfold tFidelity
  constructor
  · exact (tDirectionFidelity_mem_Icc rho tReference).1.trans
      (Finset.le_sup' (tDirectionFidelity rho) (Finset.mem_univ tReference))
  · exact Finset.sup'_le _ _ fun d _ =>
      (tDirectionFidelity_mem_Icc rho d).2
end QEC.Distillation.OneQubitMagic
