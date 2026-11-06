-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.nestedTensorPower_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:59:02.841918+00:00
-- url     : https://prove2.me/submissions/c5a55456-0fd9-4f59-b934-b8298b24c69d

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete


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
theorem _root_.solution (I : FiniteInstrument kappa Omega H K)
    (hI : I.kraus.Complete) (branches depth : Nat) :
    (nestedTensorPower I branches depth).kraus.Complete := by
  induction depth generalizing kappa Omega H K with
  | zero => exact hI
  | succ depth ih =>
      exact ih (I.tensorPower branches) (I.tensorPower_complete hI branches)
end QEC.Semantics.FiniteInstrument
