-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_redSys_mem_iff_86fd0f13e95d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:04.942036+00:00
-- url     : https://prove2.me/submissions/847d0136-109f-4953-b8c2-a163bb53777e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LineBundleRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLineBundleRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redAt_isUnit_of_isUnit_e99246644bde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_redSys_iff_92a10ff1c7af


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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp
variable {γ : Ω} {Q : LineBundle k x}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hg : RedGood hxy Q.toSubSystem γ) (I J : Chart y) (h : I.1 ⊆ J.1) (z : K') :
    z ∈ (redSys hxy Q.toSubSystem γ).sub J ↔ ∃ c : chartRing k y I, IsUnit (chartIncl h c) ∧
      (c : K') • z ∈ (redSys hxy Q.toSubSystem γ).sub I := by
  constructor
  · intro hz
    obtain ⟨q, hq, rfl⟩ := (mem_redSys_iff hsp hxy hg J z).mp hz
    obtain ⟨b, hb, hbq⟩ := (Q.mem_iff (liftChart hxy I) (liftChart hxy J) h q).mp hq
    obtain ⟨hbL, b', hb'A, hbb'⟩ := redAt_isUnit_of_isUnit hsp hxy h b hb
    have hbI := (chartRing_sub_locAt hsp hxy I b.2).2
    refine ⟨⟨_, hbI⟩, IsUnit.of_mul_eq_one ⟨b', hb'A⟩ (Subtype.ext hbb'), ?_⟩
    rw [smul_eq_mul] at hbq
    change redAt k x y b * redAt k x y (q / γ) ∈ (redSys hxy Q.toSubSystem γ).sub I
    rw [← (locAt_mul hsp hbL (hg J q hq)).2, ← mul_div_assoc]
    exact Submodule.subset_span ⟨_, hbq, rfl⟩
  · rintro ⟨c, hc, hcz⟩
    obtain ⟨c', hc'⟩ := hc.exists_left_inv
    have hc'' : (c' : K') * (c : K') = 1 := congrArg Subtype.val hc'
    have := Submodule.smul_mem _ c' ((redSys hxy Q.toSubSystem γ).mono I J h _ hcz)
    rwa [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hc'', one_mul] at this
end GroundTheory.Heights₂.Heights.Kleiman
