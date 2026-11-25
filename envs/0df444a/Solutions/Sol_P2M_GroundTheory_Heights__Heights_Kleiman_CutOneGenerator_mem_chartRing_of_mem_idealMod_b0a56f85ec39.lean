-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_mem_chartRing_of_mem_idealMod_b0a56f85ec39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:56.648799+00:00
-- url     : https://prove2.me/submissions/94a74eb5-d8dd-4b6c-8f5d-ec05a177f766

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GlobalFunctionsIntegralSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestriction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutOneGenerator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
namespace GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
theorem _root_.solution {pp : Ideal (Poly k N)} {I : Chart x} {a : Ω}
    (ha : a ∈ idealMod (x := x) pp I) : a ∈ chartRing k x I := by
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨f, s, e, -, hs, hf, hse, rfl⟩ := ha; exact ⟨f, s, e, hs, hf, hse, rfl⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact mul_mem c.2 ha
end GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
