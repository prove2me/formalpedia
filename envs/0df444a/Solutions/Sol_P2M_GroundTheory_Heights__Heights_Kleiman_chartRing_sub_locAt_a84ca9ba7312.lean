-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:49.93391+00:00
-- url     : https://prove2.me/submissions/6301246e-db01-438b-a65f-7dc0c2506918

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_locAt_48cfe111c0a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redAt_eq_fa1134abb51b

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
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')
variable {k x y}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I : Chart y) {a : Ω}
    (ha : a ∈ chartRing k x (liftChart hxy I)) :
    a ∈ locAt k x y ∧ redAt k x y a ∈ chartRing k y I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  have hsy : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos I hs
  exact ⟨mem_locAt hf hse hsy, by rw [redAt_eq hsp hf hse hsy]; exact ⟨f, s, e, hs, hf, hse, rfl⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman
