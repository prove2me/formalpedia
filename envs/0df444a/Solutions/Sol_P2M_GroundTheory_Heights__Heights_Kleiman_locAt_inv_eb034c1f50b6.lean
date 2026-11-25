-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locAt_inv_eb034c1f50b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:18:16.332689+00:00
-- url     : https://prove2.me/submissions/a585c6c3-64dc-4c6c-930e-24c3627f1d28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_aeval_ne_zero_of_primeOf_le_25245e7237d9
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
theorem _root_.solution {a : Ω} (ha : a ∈ locAt k x y) (hr : redAt k x y a ≠ 0) :
    a ≠ 0 ∧ a⁻¹ ∈ locAt k x y ∧ redAt k x y a⁻¹ = (redAt k x y a)⁻¹ := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  rw [redAt_eq hsp hf hs hsy] at hr
  have hfy : aeval y f ≠ 0 := fun h => hr (by rw [h, zero_div])
  have hfx := aeval_ne_zero_of_primeOf_le hsp hf hfy
  have hsx := aeval_ne_zero_of_primeOf_le hsp hs hsy
  refine ⟨div_ne_zero hfx hsx, by rw [inv_div]; exact mem_locAt hs hf hfy, ?_⟩
  rw [inv_div, redAt_eq hsp hs hf hfy, redAt_eq hsp hf hs hsy, inv_div]
end GroundTheory.Heights₂.Heights.Kleiman
