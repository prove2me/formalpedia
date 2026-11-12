-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hFidelity_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:18:25.429331+00:00
-- url     : https://prove2.me/submissions/f8d8adb6-28c6-497c-b721-345b035efb7a

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hDirectionFidelity_mem_Icc

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (rho : DensityOperator QubitSpace) :
    hFidelity rho ∈ Set.Icc 0 1 := by
  unfold hFidelity
  constructor
  · exact (hDirectionFidelity_mem_Icc rho hReference).1.trans
      (Finset.le_sup' (hDirectionFidelity rho) (Finset.mem_univ hReference))
  · exact Finset.sup'_le _ _ fun d _ =>
      (hDirectionFidelity_mem_Icc rho d).2
end QEC.Distillation.OneQubitMagic
