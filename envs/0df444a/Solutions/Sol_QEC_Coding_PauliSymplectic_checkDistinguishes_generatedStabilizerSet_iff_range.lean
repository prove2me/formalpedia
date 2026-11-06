-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.checkDistinguishes_generatedStabilizerSet_iff_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:26:57.787133+00:00
-- url     : https://prove2.me/submissions/2e0edcc6-0cd0-4aa9-bc46-135de8bce5bd

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_inStabilizerNormalizer_iff_commutes_generators

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    checkDistinguishes (generatedStabilizerSet generators) E ↔
      checkDistinguishes (Set.range generators) E := by
  constructor
  · rintro ⟨S, hS, hNotCommutes⟩
    by_contra hRange
    have hNormalizer : InStabilizerNormalizer generators E :=
      (inStabilizerNormalizer_iff_commutes_generators generators E).2 (by
        intro j
        by_contra hNotGenerator
        exact hRange ⟨generators j, ⟨j, rfl⟩, hNotGenerator⟩)
    exact hNotCommutes (hNormalizer S hS)
  · rintro ⟨M, ⟨j, rfl⟩, hNotCommutes⟩
    exact ⟨generators j, GeneratedStabilizer.generator j, hNotCommutes⟩
end QEC.Coding.PauliSymplectic
