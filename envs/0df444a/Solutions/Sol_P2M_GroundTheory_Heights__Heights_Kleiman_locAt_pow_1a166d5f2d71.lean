-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locAt_pow_1a166d5f2d71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:57:23.788171+00:00
-- url     : https://prove2.me/submissions/08148c6a-7008-479b-a201-b7b1f38f534c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_one_d19ae30e21d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9

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
theorem _root_.solution {a : Ω} (ha : a ∈ locAt k x y) (n : ℕ) :
    a ^ n ∈ locAt k x y ∧ redAt k x y (a ^ n) = redAt k x y a ^ n := by
  induction n with
  | zero => simpa using locAt_one hsp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := locAt_mul hsp ih.1 ha
    rw [pow_succ, pow_succ]
    exact ⟨h1, by rw [h2, ih.2]⟩
end GroundTheory.Heights₂.Heights.Kleiman
