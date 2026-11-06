-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerCoordinateOperator_mapDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:20:51.534488+00:00
-- url     : https://prove2.me/submissions/12d54fbe-0ec1-414b-a2b8-e0d1f346143b

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] :
    forall (attempts : Nat)
      (rho : DensityOperator (tensorPowerCarrier H attempts))
      (trial : Fin attempts),
      (tensorPowerCoordinateOperator attempts trial).mapDensity rho =
        tensorPowerInputMarginal attempts rho trial := by
  intro attempts
  induction attempts with
  | zero =>
      intro rho trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro rho trial
      refine Fin.cases ?_ ?_ trial
      · rfl
      · intro tailTrial
        change
          (tensorPowerCoordinateOperator attempts tailTrial).mapDensity
              (DensityOperator.leftMarginal rho) =
            tensorPowerInputMarginal attempts
              (DensityOperator.leftMarginal rho) tailTrial
        exact ih (DensityOperator.leftMarginal rho) tailTrial
end QEC.Semantics.FiniteInstrument
