-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_twist_95103f7b6497
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:52.987463+00:00
-- url     : https://prove2.me/submissions/c9f7ebe1-5e97-4905-90db-c4f9a8ac9f34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_twist_pow_sub_866f2c84b38e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9


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
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
theorem _root_.solution (G H : SubSystem S x Ω) {h g : Ω} (I : Chart x) (hg : g ∈ G.sub I) {u : Ω}
    (hu : u ∈ ampleChart H 1 h I) : u ∈ ampleChart (G.twist H) 1 (h * g) I := by
  obtain ⟨n, hn⟩ := hu
  refine ⟨n, ?_⟩
  rw [one_mul] at hn ⊢
  rw [SubSystem.pow_sub] at hn
  rw [twist_pow_sub, mul_pow]
  have : u * (h * g) ^ n = (u * h ^ n) * g ^ n := by ring
  rw [this]
  exact Submodule.mul_mem_mul hn (Submodule.pow_mem_pow _ hg n)
end GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
