-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:48.662731+00:00
-- url     : https://prove2.me/submissions/788b4d22-4c27-4b54-896a-cda0fb624cec

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
theorem _root_.solution {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) :
    a * b ∈ locAt k x y ∧ redAt k x y (a * b) = redAt k x y a * redAt k x y b := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  obtain ⟨f', s', e', hf', hs', hsy', rfl⟩ := hb
  have hprod : aeval x f / aeval x s * (aeval x f' / aeval x s') =
      aeval x (f * f') / aeval x (s * s') := by
    rw [div_mul_div_comm]; simp only [map_mul]
  have hss : aeval y (s * s') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hsy hsy'
  rw [hprod]
  refine ⟨mem_locAt (hf.mul hf') (hs.mul hs') hss, ?_⟩
  rw [redAt_eq hsp (hf.mul hf') (hs.mul hs') hss, redAt_eq hsp hf hs hsy, redAt_eq hsp hf' hs' hsy',
    div_mul_div_comm]
  simp only [map_mul]
end GroundTheory.Heights₂.Heights.Kleiman
