-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.toFiniteInstrument_sum_bornWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:49:57.847896+00:00
-- url     : https://prove2.me/submissions/9d1a03d5-2771-4ad9-96ca-765bc2654ca6

import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one


set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.QuantumChannel
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.QuantumChannel
theorem _root_.solution (Φ : QuantumChannel H K)
    (rho : DensityOperator H) :
    ∑ outcome, (Φ.toFiniteInstrument).bornWeight outcome rho = 1 :=
  (Φ.toFiniteInstrument).sum_bornWeight_eq_one Φ.toFiniteInstrument_complete rho
end QEC.Semantics.QuantumChannel
