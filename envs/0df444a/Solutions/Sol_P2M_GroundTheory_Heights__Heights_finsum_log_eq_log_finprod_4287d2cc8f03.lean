-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finsum_log_eq_log_finprod_4287d2cc8f03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:08:39.849805+00:00
-- url     : https://prove2.me/submissions/b65ac2d7-b8a1-4241-ac1f-671d0c6edb4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {α : Type*} {f : α → ℝ} (hpos : ∀ a, 0 < f a)
    (hf : Function.HasFiniteMulSupport f) : ∑ᶠ a, Real.log (f a) = Real.log (∏ᶠ a, f a) := by
  have hf' : (Function.mulSupport f).Finite := hf
  have hs : Function.support (fun a ↦ Real.log (f a)) ⊆ hf'.toFinset := by
    intro a ha
    rw [Set.Finite.coe_toFinset]
    intro h1
    exact ha (by show Real.log (f a) = 0; rw [h1, Real.log_one])
  rw [finsum_eq_sum_of_support_subset _ hs,
    finprod_eq_prod_of_mulSupport_subset (s := hf'.toFinset) f (by rw [Set.Finite.coe_toFinset]),
    Real.log_prod fun a _ ↦ (hpos a).ne']
end GroundTheory.Heights₂.Heights
