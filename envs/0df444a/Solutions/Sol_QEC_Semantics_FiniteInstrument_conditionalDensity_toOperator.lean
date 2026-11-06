-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:21:12.1692+00:00
-- url     : https://prove2.me/submissions/f0f09e01-4bf5-42c0-b8de-ad464b1a90da

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Instruments_Core

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
attribute [local instance] QEC.Semantics.FiniteInstrument._p2m_local_instance_a5f1a79248_39
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (I : FiniteInstrument κ Ω H K)
    (outcome : Ω) (rho : DensityOperator H)
    (hpos : 0 < I.bornWeight outcome rho) :
    (I.conditionalDensity outcome rho hpos).toOperator =
      ((I.bornWeight outcome rho : Complex)⁻¹) •
        I.branchOperator outcome rho.toOperator :=
  rfl
end QEC.Semantics.FiniteInstrument
