-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.correctedBy_iff_correctable_toQuantumChannel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:08:39.772899+00:00
-- url     : https://prove2.me/submissions/005f1b41-5be3-4ed4-9bdf-0f4dacdfd4cf

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H K) (hE : E.Complete)
    (C : QuantumCode H) (recovery : QuantumChannel K H) :
    E.CorrectedBy C recovery ↔ Correctable H K C (E.toQuantumChannel hE) recovery := by
  rfl
end QEC.Semantics.FiniteKrausFamily
