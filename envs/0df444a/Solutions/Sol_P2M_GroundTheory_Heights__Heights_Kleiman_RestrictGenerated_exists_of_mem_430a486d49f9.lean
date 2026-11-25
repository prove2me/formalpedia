-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_exists_of_mem_430a486d49f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:07.615035+00:00
-- url     : https://prove2.me/submissions/e92e995f-ec47-4399-8b9f-cd113bdacc0f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_zero_1acae039ee44

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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
theorem _root_.solution {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ w ∈ Q.sub (liftChart hxy J), r w = t := by
  rw [← h.span J] at ht
  induction ht using Submodule.span_induction with
  | mem t ht => obtain ⟨w, hw, rfl⟩ := ht; exact ⟨w, hw, rfl⟩
  | zero => exact ⟨0, zero_mem _, r_zero h J⟩
  | add t t' _ _ ht ht' =>
    obtain ⟨w, hw, rfl⟩ := ht
    obtain ⟨w', hw', rfl⟩ := ht'
    exact ⟨w + w', add_mem hw hw', h.add J w hw w' hw'⟩
  | smul b t _ ht =>
    obtain ⟨w, hw, rfl⟩ := ht
    obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
    let a : chartRing S x (liftChart hxy J) := ⟨aeval x f / aeval x s, f, s, e, hs, hf, hse, rfl⟩
    refine ⟨a • w, (Q.sub _).smul_mem a hw, ?_⟩
    show r (aeval x f / aeval x s * w) = (b : K') * r w
    rw [h.smul J w hw f s e hs hf hse, hb]
end GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
