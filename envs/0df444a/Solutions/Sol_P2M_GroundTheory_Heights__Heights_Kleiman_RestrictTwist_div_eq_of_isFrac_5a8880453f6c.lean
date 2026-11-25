-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_div_eq_of_isFrac_5a8880453f6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:22:01.230697+00:00
-- url     : https://prove2.me/submissions/b404426d-d2d5-4342-b613-a23ccf59877e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
theorem _root_.solution {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) {c : ℤ} {I J : Finset (Fin (N + 1))} {z : Ω}
    {t t' : Poly S N × Poly S N × ℕ × ℕ} (h : IsFrac x c I z t) (h' : IsFrac x c J z t')
    (hx : aeval x t.2.1 ≠ 0) (hx' : aeval x t'.2.1 ≠ 0) (hy : aeval y t.2.1 ≠ 0)
    (hy' : aeval y t'.2.1 ≠ 0) :
    aeval y t.1 / aeval y t.2.1 = aeval y t'.1 / aeval y t'.2.1 := by
  obtain ⟨f, s, e, e'⟩ := t
  obtain ⟨f', s', d, d'⟩ := t'
  obtain ⟨-, hf, hs, hc, hz⟩ := h
  obtain ⟨-, hf', hs', hc', hz'⟩ := h'
  dsimp only at hf hs hc hz hf' hs' hc' hz' hx hx' hy hy' ⊢
  have hdeg : d' + e = e' + d := by omega
  have hg : (f * s' - f' * s).IsHomogeneous (e' + d) :=
    (hf.mul hs').sub (by rw [← hdeg]; exact hf'.mul hs)
  have hx0 : aeval x (f * s' - f' * s) = 0 := by
    have := hz.symm.trans hz'
    rw [div_eq_div_iff hx hx'] at this
    rw [map_sub, map_mul, map_mul, this, sub_self]
  have hy0 := (mem_primeOf_of_isHomogeneous y hg).mp (hle ((mem_primeOf_of_isHomogeneous x hg).mpr hx0))
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at hy0
  rw [div_eq_div_iff hy hy', hy0]
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
