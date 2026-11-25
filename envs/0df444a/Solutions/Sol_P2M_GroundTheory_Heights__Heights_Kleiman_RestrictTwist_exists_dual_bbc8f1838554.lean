-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_dual_bbc8f1838554
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:22:43.219821+00:00
-- url     : https://prove2.me/submissions/23e49022-7b3e-4ce3-9e53-a01954f083c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_list_of_mem_mul_9dade8467f93

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
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {x : Fin (N + 1) → Ω} (Q : LineBundle S x) (I : Chart x) :
    ∃ l : List (Ω × Ω), (∀ p ∈ l, p.1 ∈ Q.sub I ∧ ∀ a ∈ Q.sub I, p.2 * a ∈ chartRing S x I) ∧
      (l.map fun p => p.1 * p.2).sum = 1 := by
  obtain ⟨Q', hQ'⟩ := Q.invertible I
  have h1 : (1 : Ω) ∈ Q.sub I * Q' := by
    rw [hQ']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨l, hl, hsum⟩ := exists_list_of_mem_mul h1
  refine ⟨l, fun p hp => ⟨(hl p hp).1, fun a ha => ?_⟩, hsum⟩
  have h2 : p.2 * a ∈ Q.sub I * Q' := by
    rw [mul_comm p.2 a]; exact Submodule.mul_mem_mul ha (hl p hp).2
  rw [hQ'] at h2
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp h2
  rw [← hb]; exact b.2
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
