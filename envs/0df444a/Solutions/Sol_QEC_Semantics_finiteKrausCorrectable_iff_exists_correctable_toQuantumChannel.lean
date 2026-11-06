-- Prove2me | solution 1 for QEC.Semantics.finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:32:48.192945+00:00
-- url     : https://prove2.me/submissions/4678e331-4c46-41e2-8ecf-91d241498dc4

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_correctedBy_iff_correctable_toQuantumChannel

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
namespace QEC.Semantics
theorem _root_.solution
    {ι : Type v} [Fintype ι] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (C : QuantumCode H) (noise : FiniteKrausFamily ι H K)
    (recovery : QuantumChannel K H) :
    FiniteKrausCorrectable ι H K C noise recovery ↔
      ∃ hnoise : noise.Complete,
        Correctable H K C (noise.toQuantumChannel hnoise) recovery := by
  constructor
  · intro h
    exact ⟨h.1, (noise.correctedBy_iff_correctable_toQuantumChannel h.1 C recovery).1 h.2⟩
  · rintro ⟨hnoise, hcorrectable⟩
    exact ⟨hnoise,
      (noise.correctedBy_iff_correctable_toQuantumChannel hnoise C recovery).2 hcorrectable⟩
end QEC.Semantics
