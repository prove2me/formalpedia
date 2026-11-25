-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_redGood_twist_a17ebf2d3318
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:51:57.178886+00:00
-- url     : https://prove2.me/submissions/8a64d006-20a1-430f-a019-1a1d0d452347

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_zero_68297b898f07


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
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {P Q : SubSystem k x Ω} {γ δ : Ω} (hP : RedGood hxy P γ)
    (hQ : RedGood hxy Q δ) : RedGood hxy (P.twist Q) (γ * δ) := by
  intro I z hz
  refine Submodule.span_induction (p := fun z _ => z / (γ * δ) ∈ locAt k x y) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, p, hp, rfl⟩
    have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
    rw [this]; exact (locAt_mul hsp (hQ I q hq) (hP I p hp)).1
  · rw [zero_div]; exact (locAt_zero hsp).1
  · intro u v _ _ hu hv; rw [add_div]; exact (locAt_add hsp hu hv).1
  · intro c u _ hu
    rw [chartRing_smul_def, mul_div_assoc]
    exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 hu).1
end GroundTheory.Heights₂.Heights.Kleiman
