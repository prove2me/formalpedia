-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_symm_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:41:47.270597+00:00
-- url     : https://prove2.me/submissions/3a12c4df-f4c9-427f-8d5c-03c8865f9bec

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
    (iota : Type u) [Fintype iota] (attempts : Nat)
    (bits : Qubit.Bitstring (Fin attempts × iota))
    (trial : Fin attempts) (site : iota) :
    tensorPowerHistoryAt (Qubit.Bitstring iota) attempts
        ((tensorPowerQubitBitstringEquiv iota attempts).symm bits) trial site =
      bits (trial, site) := by
  exact congrFun
    ((tensorPowerQubitBitstringEquiv iota attempts).apply_symm_apply bits)
    (trial, site)
end QEC.Semantics.FiniteInstrument
