-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LocF_isLocalField_abf02d17db6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:50:10.371028+00:00
-- url     : https://prove2.me/submissions/987da6a0-face-4716-b000-f359f6c074d9

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_vcompat_8cc30d9947af
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_proper_d65cdbdea1a5

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
namespace Formalism.BasicNotions.Examples₂.LocF
theorem _root_.solution : letI := vrel v; IsNonarchimedeanLocalField (v.adicCompletion F) := by
  let _ := vrel v
  have := vcompat v
  have := proper v
  have h1 : IsValuativeTopology (v.adicCompletion F) :=
    IsValuativeTopology.of_mem_nhds_iff_vle (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
      (fun {s x} => Valued.mem_nhds)
  have h2 : ValuativeRel.IsNontrivial (v.adicCompletion F) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).mpr inferInstance
  exact { }
end Formalism.BasicNotions.Examples₂.LocF
