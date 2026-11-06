-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.nestedTensorPower_sum_bornWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:24:32.881849+00:00
-- url     : https://prove2.me/submissions/5a5de010-7f6b-4c26-9efb-50a5503f267a

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorPower_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one


set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (branches depth : Nat)
    (rho : DensityOperator (nestedTensorCarrier H branches depth)) :
    ∑ outcome, (nestedTensorPower I branches depth).bornWeight outcome rho = 1 :=
  (nestedTensorPower I branches depth).sum_bornWeight_eq_one
    (nestedTensorPower_complete I hI branches depth) rho
end QEC.Semantics.FiniteInstrument
