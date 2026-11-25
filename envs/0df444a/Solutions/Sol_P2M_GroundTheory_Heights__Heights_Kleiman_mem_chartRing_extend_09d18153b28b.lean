-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_extend_09d18153b28b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:59:07.016661+00:00
-- url     : https://prove2.me/submissions/17225301-e44e-4c69-b680-24de0544b91e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_map_mem_monos_1c3de4584cdf

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
open scoped Pointwise
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ chartRing F x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  exact ⟨map (algebraMap S F) f, map (algebraMap S F) s, e, map_mem_monos hs, hf.map _, hse.map _,
    by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩
end GroundTheory.Heights₂.Heights.Kleiman
