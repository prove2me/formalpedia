-- Prove2me | solution 1 for QEC.Semantics.exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:53.899561+00:00
-- url     : https://prove2.me/submissions/7983c307-fdf5-40f6-9ac1-61669de4cbdc

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel

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
    (C : QuantumCode H) (noise : FiniteKrausFamily ι H K) :
    (∃ recovery : QuantumChannel K H,
        FiniteKrausCorrectable ι H K C noise recovery) ↔
      ∃ hnoise : noise.Complete,
        ∃ recovery : QuantumChannel K H,
          Correctable H K C (noise.toQuantumChannel hnoise) recovery := by
  constructor
  · rintro ⟨recovery, hcorrectable⟩
    rcases (finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
      C noise recovery).1 hcorrectable with ⟨hnoise, hbundled⟩
    exact ⟨hnoise, recovery, hbundled⟩
  · rintro ⟨hnoise, recovery, hbundled⟩
    exact ⟨recovery,
      (finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel C noise recovery).2
        ⟨hnoise, hbundled⟩⟩
end QEC.Semantics
