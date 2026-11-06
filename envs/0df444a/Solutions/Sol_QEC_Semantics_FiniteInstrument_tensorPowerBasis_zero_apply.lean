-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:48:59.515235+00:00
-- url     : https://prove2.me/submissions/cebb84ce-59b2-4553-a14c-6737a7faf87a

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped TensorProduct
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable {β : Type v} [Fintype β]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (b : OrthonormalBasis β Complex H)
    (index : PUnit) :
    tensorPowerBasis b 0 index =
      EuclideanSpace.basisFun (ULift.{u} (Fin 1)) Complex
        ((Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit).symm index) := by
  change ((EuclideanSpace.basisFun (ULift.{u} (Fin 1)) Complex).reindex
    (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit)) index = _
  rw [OrthonormalBasis.reindex_apply]
end QEC.Semantics.FiniteInstrument
