-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_mul_mem_of_mem_mul_89319747f3eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:24:41.891741+00:00
-- url     : https://prove2.me/submissions/2542bb4f-6fb6-42a1-8c50-884aae83a939

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_mul_mem__7be37290911c

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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {Q₁ Q₂ : SubSystem S x Ω} {I : Chart x} {v z : Ω}
    (hv : ∀ a ∈ Q₁.sub I, v * a ∈ chartRing S x I) (hz : z ∈ Q₂.sub I * Q₁.sub I) :
    v * z ∈ Q₂.sub I := by
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem b hb a ha =>
    rw [show v * (b * a) = (v * a) * b by ring]; exact mul_mem' (hv a ha) hb
  | add z _ z' _ h h' => rw [mul_add]; exact add_mem h h'
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
