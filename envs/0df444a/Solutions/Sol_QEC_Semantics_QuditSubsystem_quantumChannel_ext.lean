-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.quantumChannel_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:48:45.15378+00:00
-- url     : https://prove2.me/submissions/ab46ecad-d23f-4d1f-aa7d-5246d8970591

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi Psi : QuantumChannel H K) (h : Phi.toLinearMap = Psi.toLinearMap) : Phi = Psi := by
  cases Phi
  cases Psi
  cases h
  rfl
end QEC.Semantics.QuditSubsystem
