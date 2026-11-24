-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LocF_emb_cont_73c680fc7d35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:50:16.746836+00:00
-- url     : https://prove2.me/submissions/1296928b-c80a-426d-8bf5-a12d8e189e7d

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LocF
open NumberField IsDedekindDomain HeightOneSpectrum WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable (l : ℕ) [hl : Fact l.Prime] (hv : (l : 𝓞 F) ∈ v.asIdeal)
namespace Formalism.BasicNotions.Examples₂.LocF
theorem _root_.solution : Continuous (emb v l hv) :=
  (uniformContinuous_uniformly_extend (iQ_ind l) (iQ_dense l) (fQ_uc v l hv)).continuous
end Formalism.BasicNotions.Examples₂.LocF
