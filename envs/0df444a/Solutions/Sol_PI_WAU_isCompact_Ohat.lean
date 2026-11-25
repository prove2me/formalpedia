-- Prove2me | solution 1 for PI.WAU.isCompact_Ohat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:41.958217+00:00
-- url     : https://prove2.me/submissions/b4cf7f8a-90a6-4f1a-b192-cf64f3fa0569

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology
variable {F : Type} [Field F] [NumberField F]
namespace PI.WAU
theorem _root_.solution : IsCompact (Ohat F) := by
  have hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have : Ohat F = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, rfl⟩
    · rintro ⟨x, rfl⟩ v
      exact (x v).2
  rw [this]
  exact isCompact_range hc
end PI.WAU
