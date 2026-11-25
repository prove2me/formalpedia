-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:51.024969+00:00
-- url     : https://prove2.me/submissions/1f1468fd-305b-4a7b-ab47-aec87f1a264e

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
theorem _root_.solution {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) :
    a + b ∈ locAt k x y ∧ redAt k x y (a + b) = redAt k x y a + redAt k x y b := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  obtain ⟨f', s', e', hf', hs', hsy', rfl⟩ := hb
  have hsx := aeval_ne_zero_of_primeOf_le hsp hs hsy
  have hsx' := aeval_ne_zero_of_primeOf_le hsp hs' hsy'
  have hhom : (f * s' + s * f').IsHomogeneous (e + e') := (hf.mul hs').add (hs.mul hf')
  have hsum : aeval x f / aeval x s + aeval x f' / aeval x s' =
      aeval x (f * s' + s * f') / aeval x (s * s') := by
    rw [div_add_div _ _ hsx hsx']; simp only [map_add, map_mul]
  have hss : aeval y (s * s') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hsy hsy'
  rw [hsum]
  refine ⟨mem_locAt hhom (hs.mul hs') hss, ?_⟩
  rw [redAt_eq hsp hhom (hs.mul hs') hss, redAt_eq hsp hf hs hsy, redAt_eq hsp hf' hs' hsy',
    div_add_div _ _ hsy hsy']
  simp only [map_add, map_mul]
end GroundTheory.Heights₂.Heights.Kleiman
